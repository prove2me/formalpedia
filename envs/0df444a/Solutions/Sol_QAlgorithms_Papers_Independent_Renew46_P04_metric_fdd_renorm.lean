-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.metric_fdd_renorm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:02:46.812635+00:00
-- url     : https://prove2.me/submissions/9ef8ab02-06c6-40e8-977b-2a7f2bfd3f62

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

open Filter Set
open scoped Topology ENNReal

namespace X7FddRenorm

variable {K : Type*} [RCLike K] {X : Type} [NormedAddCommGroup X] [NormedSpace K X]

/-- Sequence space of partial-sum sequences, inside l-infinity. -/
def X7_S (K : Type*) [RCLike K] [NormedSpace K X] (e : ℕ → X) :
    Submodule K (lp (fun _ : ℕ => X) ∞) where
  carrier := {s | (s : ℕ → X) 0 = 0 ∧ (∀ n, (s : ℕ → X) (n + 1) - (s : ℕ → X) n ∈ K ∙ e n) ∧
    CauchySeq (s : ℕ → X)}
  zero_mem' := by
    refine ⟨rfl, fun n => by simp, ?_⟩
    show CauchySeq (fun _ : ℕ => (0 : X))
    exact cauchySeq_const 0
  add_mem' := by
    rintro a b ⟨ha0, ha1, ha2⟩ ⟨hb0, hb1, hb2⟩
    refine ⟨by simp [lp.coeFn_add, ha0, hb0], fun n => ?_, ?_⟩
    · have := Submodule.add_mem _ (ha1 n) (hb1 n)
      simp only [lp.coeFn_add, Pi.add_apply]
      convert this using 1; abel
    · simp only [lp.coeFn_add]; exact ha2.add hb2
  smul_mem' := by
    rintro c a ⟨ha0, ha1, ha2⟩
    refine ⟨by simp [lp.coeFn_smul, ha0], fun n => ?_, ?_⟩
    · have := Submodule.smul_mem _ c (ha1 n)
      simp only [lp.coeFn_smul, Pi.smul_apply]
      convert this using 1; rw [smul_sub]
    · simp only [lp.coeFn_smul]; exact (uniformContinuous_const_smul c).comp_cauchySeq ha2

theorem X7_eval_cont (m : ℕ) : Continuous (fun s : lp (fun _ : ℕ => X) ∞ => (s : ℕ → X) m) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun a b => ?_).continuous
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have := lp.norm_apply_le_norm (p := ∞) (by simp) (a - b) m
  simpa [lp.coeFn_sub] using this

theorem X7_cauchy_closed :
    IsClosed {s : lp (fun _ : ℕ => X) ∞ | CauchySeq (s : ℕ → X)} := by
  refine isClosed_of_closure_subset fun s hs => ?_
  rw [Metric.mem_closure_iff] at hs
  show CauchySeq _
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨t, ht, hst⟩ := hs (ε / 3) (by linarith)
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.mp ht) (ε / 3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ∀ m, dist ((s : ℕ → X) m) ((t : ℕ → X) m) < ε / 3 := fun m => by
    rw [dist_eq_norm]
    have := lp.norm_apply_le_norm (p := ∞) (by simp) (s - t) m
    rw [lp.coeFn_sub] at this
    rw [dist_eq_norm] at hst
    exact lt_of_le_of_lt this hst
  calc dist ((s : ℕ → X) n) ((s : ℕ → X) N)
      ≤ dist ((s : ℕ → X) n) ((t : ℕ → X) n) + dist ((t : ℕ → X) n) ((t : ℕ → X) N)
          + dist ((t : ℕ → X) N) ((s : ℕ → X) N) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := hN n hn
        have h2 := h1 N
        rw [dist_comm] at h2
        linarith [h1 n]
    _ = ε := by ring

theorem X7_S_closed (e : ℕ → X) : IsClosed ((X7_S K e : Submodule K _) : Set (lp (fun _ : ℕ => X) ∞)) := by
  have h0 : IsClosed {s : lp (fun _ : ℕ => X) ∞ | (s : ℕ → X) 0 = 0} :=
    isClosed_eq (X7_eval_cont 0) continuous_const
  have h1 : IsClosed {s : lp (fun _ : ℕ => X) ∞ |
      ∀ n, (s : ℕ → X) (n + 1) - (s : ℕ → X) n ∈ K ∙ e n} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun n => ?_
    exact (Submodule.closed_of_finiteDimensional (K ∙ e n)).preimage
      ((X7_eval_cont (n + 1)).sub (X7_eval_cont n))
  have : ((X7_S K e : Submodule K _) : Set (lp (fun _ : ℕ => X) ∞)) =
      {s : lp (fun _ : ℕ => X) ∞ | (s : ℕ → X) 0 = 0} ∩
        ({s : lp (fun _ : ℕ => X) ∞ | ∀ n, (s : ℕ → X) (n + 1) - (s : ℕ → X) n ∈ K ∙ e n} ∩
        {s : lp (fun _ : ℕ => X) ∞ | CauchySeq (s : ℕ → X)}) := by
    ext s; rfl
  rw [this]
  exact h0.inter (h1.inter X7_cauchy_closed)

variable [CompleteSpace X]

instance X7_S_complete (e : ℕ → X) : CompleteSpace (X7_S K e) :=
  completeSpace_coe_iff_isComplete.mpr (X7_S_closed e).isComplete

/-- underlying sequence -/
def sq {e : ℕ → X} (s : X7_S K e) : ℕ → X := ((s : lp (fun _ : ℕ => X) ∞) : ℕ → X)

theorem sq_norm_le {e : ℕ → X} (s : X7_S K e) (m : ℕ) : ‖sq s m‖ ≤ ‖s‖ :=
  lp.norm_apply_le_norm (p := ∞) (by simp) _ m

theorem sq_tendsto {e : ℕ → X} (s : X7_S K e) :
    Tendsto (sq s) atTop (𝓝 (limUnder atTop (sq s))) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete s.2.2.2)

/-- The limit map. -/
def limL (e : ℕ → X) : X7_S K e →L[K] X :=
  LinearMap.mkContinuous
    { toFun := fun s => limUnder atTop (sq s)
      map_add' := fun a b => by
        have : sq (a + b) = sq a + sq b := by funext m; rfl
        show limUnder atTop (sq (a + b)) = _
        rw [this]; exact ((sq_tendsto a).add (sq_tendsto b)).limUnder_eq
      map_smul' := fun c a => by
        have h := (sq_tendsto a).const_smul c
        have : sq (c • a) = c • sq a := by funext m; rfl
        simp only [RingHom.id_apply]
        rw [this]; exact h.limUnder_eq }
    1 (fun s => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact le_of_tendsto (sq_tendsto s).norm (Eventually.of_forall fun m => sq_norm_le s m))

theorem limL_tendsto (e : ℕ → X) (s : X7_S K e) : Tendsto (sq s) atTop (𝓝 (limL e s)) :=
  sq_tendsto s

theorem X7_telescope {e : ℕ → X} (s : X7_S K e) (c : ℕ → K)
    (hc : ∀ n, sq s (n + 1) - sq s n = c n • e n) (n : ℕ) :
    sq s n = ∑ i ∈ Finset.range n, c i • e i := by
  induction n with
  | zero => simpa [sq] using s.2.1
  | succ n ih => rw [Finset.sum_range_succ, ← ih, ← hc n]; abel

theorem X7_coeff {e : ℕ → X} (s : X7_S K e) :
    ∃ c : ℕ → K, ∀ n, sq s (n + 1) - sq s n = c n • e n := by
  have h := fun n => Submodule.mem_span_singleton.mp (s.2.2.1 n)
  choose c hc using h
  exact ⟨c, fun n => (hc n).symm⟩

theorem sq_inj {e : ℕ → X} {s t : X7_S K e} (h : sq s = sq t) : s = t := by
  apply Subtype.ext; apply lp.ext; exact h

theorem limL_bij (e : ℕ → X) (hb : ∀ x : X, ∃! a : ℕ → K,
    Tendsto (fun n => ∑ i ∈ Finset.range n, a i • e i) atTop (𝓝 x)) :
    Function.Bijective (limL (K := K) e) := by
  constructor
  · intro s t hst
    obtain ⟨c, hc⟩ := X7_coeff s
    obtain ⟨d, hd⟩ := X7_coeff t
    have hs := limL_tendsto e s
    have ht := limL_tendsto e t
    rw [funext (X7_telescope s c hc)] at hs
    rw [funext (X7_telescope t d hd), ← hst] at ht
    have hcd : c = d := (hb (limL e s)).unique hs ht
    apply sq_inj
    funext n
    rw [X7_telescope s c hc, X7_telescope t d hd, hcd]
  · intro x
    obtain ⟨a, ha, -⟩ := hb x
    set f : ℕ → X := fun n => ∑ i ∈ Finset.range n, a i • e i with hf
    have hmem : Memℓp f ∞ := by
      rw [memℓp_infty_iff]
      exact ha.norm.bddAbove_range
    let g : lp (fun _ : ℕ => X) ∞ := ⟨f, hmem⟩
    have hgS : g ∈ X7_S K e := by
      refine ⟨by simp [g, f], fun n => ?_, ha.cauchySeq⟩
      show f (n + 1) - f n ∈ K ∙ e n
      simp only [f, Finset.sum_range_succ, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    refine ⟨⟨g, hgS⟩, ?_⟩
    have := limL_tendsto (K := K) e ⟨g, hgS⟩
    exact tendsto_nhds_unique this ha

/-- truncation -/
def truncF (n : ℕ) (f : ℕ → X) : ℕ → X := fun m => f (min m n)

theorem trunc_mem {e : ℕ → X} (n : ℕ) (s : X7_S K e) :
    Memℓp (truncF n (sq s)) ∞ := by
  rw [memℓp_infty_iff]
  exact ⟨‖s‖, by rintro _ ⟨m, rfl⟩; exact sq_norm_le s _⟩

theorem trunc_memS {e : ℕ → X} (n : ℕ) (s : X7_S K e) :
    (⟨truncF n (sq s), trunc_mem n s⟩ : lp (fun _ : ℕ => X) ∞) ∈ X7_S K e := by
  refine ⟨by simpa [truncF, sq] using s.2.1, fun m => ?_, ?_⟩
  · show truncF n (sq s) (m + 1) - truncF n (sq s) m ∈ K ∙ e m
    simp only [truncF]
    rcases lt_or_ge m n with h | h
    · rw [min_eq_left (by omega : m + 1 ≤ n), min_eq_left h.le]
      exact s.2.2.1 m
    · rw [min_eq_right (by omega : n ≤ m + 1), min_eq_right h, sub_self]
      exact Submodule.zero_mem _
  · show CauchySeq (truncF n (sq s))
    refine Tendsto.cauchySeq (x := sq s n) (tendsto_atTop_of_eventually_const (i₀ := n) fun m hm => ?_)
    simp [truncF, min_eq_right hm]


/-- truncation projection -/
def truncL (e : ℕ → X) (n : ℕ) : X7_S K e →L[K] X7_S K e :=
  LinearMap.mkContinuous
    { toFun := fun s => ⟨⟨truncF n (sq s), trunc_mem n s⟩, trunc_memS n s⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
    1 (fun s => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg s) fun m => sq_norm_le s _)

theorem sq_truncL (e : ℕ → X) (n : ℕ) (s : X7_S K e) :
    sq (truncL e n s) = truncF n (sq s) := rfl

/-- difference coordinates -/
def psiL (e : ℕ → X) (n : ℕ) : X7_S K e →ₗ[K] ((i : Fin n) → ↥(K ∙ e i)) where
  toFun s i := ⟨sq s (i + 1) - sq s i, s.2.2.1 i⟩
  map_add' a b := by
    funext i; apply Subtype.ext
    show sq (a + b) (i + 1) - sq (a + b) i = (sq a (i + 1) - sq a i) + (sq b (i + 1) - sq b i)
    have : sq (a + b) = sq a + sq b := by funext m; rfl
    rw [this]; simp only [Pi.add_apply]; abel
  map_smul' c a := by
    funext i; apply Subtype.ext
    show sq (c • a) (i + 1) - sq (c • a) i = c • (sq a (i + 1) - sq a i)
    have : sq (c • a) = c • sq a := by funext m; rfl
    rw [this, smul_sub]; rfl

theorem X7_range_fd (e : ℕ → X) (n : ℕ) :
    FiniteDimensional K (truncL (K := K) e n).range := by
  have hinj : Function.Injective ((psiL (K := K) e n).comp
      (truncL (K := K) e n).range.subtype) := by
    rintro ⟨z1, ⟨s1, rfl⟩⟩ ⟨z2, ⟨s2, rfl⟩⟩ h
    apply Subtype.ext
    apply sq_inj
    have hd : ∀ i < n, sq (truncL e n s1) (i + 1) - sq (truncL e n s1) i =
        sq (truncL e n s2) (i + 1) - sq (truncL e n s2) i := by
      intro i hi
      have := congrArg Subtype.val (congrFun h ⟨i, hi⟩)
      exact this
    have hle : ∀ m ≤ n, sq (truncL e n s1) m = sq (truncL e n s2) m := by
      intro m
      induction m with
      | zero =>
        intro _
        have z1 : sq s1 0 = 0 := s1.2.1
        have z2 : sq s2 0 = 0 := s2.2.1
        show truncF n (sq s1) 0 = truncF n (sq s2) 0
        simp [truncF, z1, z2]
      | succ m ih =>
        intro hm
        have h1 := hd m (by omega)
        have h2 := ih (by omega)
        rw [h2] at h1
        exact sub_left_injective h1
    funext m
    show truncF n (sq s1) m = truncF n (sq s2) m
    have := hle (min m n) (min_le_right _ _)
    change truncF n (sq s1) (min m n) = truncF n (sq s2) (min m n) at this
    simpa [truncF] using this
  exact Module.Finite.of_injective _ hinj

theorem X7_S_metricPi (e : ℕ → X) : QAlgorithms.Papers.Independent.Renew46.P04.MetricPi K (X7_S K e) := by
  intro eps heps s _
  have hev : ∀ x ∈ s, ∀ᶠ n in atTop, ∀ m, ‖sq x m - sq x (min m n)‖ ≤ eps / 2 := by
    intro x _
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp x.2.2.2 (eps / 4) (by linarith)
    refine eventually_atTop.2 ⟨N, fun n hn m => ?_⟩
    rcases le_total m n with h | h
    · rw [min_eq_left h, sub_self, norm_zero]; linarith
    · rw [min_eq_right h, ← dist_eq_norm]
      have h1 := hN m (by omega)
      have h2 := hN n hn
      rw [dist_comm] at h2
      change dist (sq x m) (sq x N) < eps / 4 at h1
      change dist (sq x N) (sq x n) < eps / 4 at h2
      linarith [dist_triangle (sq x m) (sq x N) (sq x n)]
  obtain ⟨n, hn⟩ := ((eventually_all_finset s).2 hev).exists
  refine ⟨truncL e n, ?_, ?_, X7_range_fd e n, fun x hx => ⟨truncL e n x, ⟨x, rfl⟩, ?_⟩⟩
  · ext1 z; apply sq_inj; funext m
    show truncF n (truncF n (sq z)) m = truncF n (sq z) m
    simp [truncF]
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · refine lt_of_le_of_lt ?_ (half_lt_self heps)
    exact lp.norm_le_of_forall_le (by linarith) fun m => hn x hx m

theorem X7_part1 {Y : Type} [NormedAddCommGroup Y] [NormedSpace K Y] :
    QAlgorithms.Papers.Independent.Renew46.P04.ContractiveFDD (K := K) (X := Y) →
      QAlgorithms.Papers.Independent.Renew46.P04.MetricPi K Y := by
  rintro ⟨P, hP1, hP2, hP3⟩ eps heps s _
  have hev : ∀ x ∈ s, ∀ᶠ n in atTop, ‖x - P n x‖ < eps := by
    intro x _
    have := (hP3 x).sub (tendsto_const_nhds (x := x))
    rw [sub_self] at this
    filter_upwards [(this.norm).eventually (gt_mem_nhds (by simpa using heps))] with n hn
    rw [norm_sub_rev]; simpa using hn
  obtain ⟨n, hn⟩ := ((eventually_all_finset s).2 hev).exists
  refine ⟨P n, by rw [hP2, min_self], (hP1 n).2, (hP1 n).1, fun x hx => ⟨P n x, ⟨x, rfl⟩, hn x hx⟩⟩

end X7FddRenorm

universe u v

variable {K : Type*} [RCLike K]

open QAlgorithms.Papers.Independent.Renew46.P04 X7FddRenorm in
theorem solution (X : Type) [NormedAddCommGroup X] [NormedSpace K X]
    [CompleteSpace X] :
    (ContractiveFDD (K := K) (X := X) → MetricPi K X) ∧
    (HasSchauderBasis (K := K) (X := X) → ∃ B : BanachData K,
      Nonempty (X ≃L[K] B.Carrier) ∧ MetricPi K B.Carrier) := by
  refine ⟨X7_part1, fun ⟨e, he⟩ => ⟨⟨X7_S K e⟩, ⟨(ContinuousLinearEquiv.ofBijective (limL (K := K) e)
    (LinearMap.ker_eq_bot.mpr (limL_bij e he).1)
    (LinearMap.range_eq_top.mpr (limL_bij e he).2)).symm⟩, X7_S_metricPi e⟩⟩
