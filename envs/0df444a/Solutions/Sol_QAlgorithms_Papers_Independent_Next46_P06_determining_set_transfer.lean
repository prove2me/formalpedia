-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P06.determining_set_transfer
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:24:22.363319+00:00
-- url     : https://prove2.me/submissions/4b4a316d-2e61-47ec-a095-c0389d541bc2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06
noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

abbrev g61c_L := lp (fun _ : ℕ => ℂ) 2

def g61c_Phi (f : ℕ → ℂ) : Graph g61c_L := {p | ∀ k, p.2 k = f k * p.1 k}

theorem g61c_ext {x y : g61c_L} (h : ∀ k, x k = y k) : x = y := lp.ext (funext h)

def g61c_diag (d : ℕ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) : g61c_L →L[ℂ] g61c_L :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun k => d k * x k, (lp.memℓp x).mono' fun k => by
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hd k)⟩
      map_add' := fun x y => g61c_ext fun k => by
        show d k * (x + y) k = d k * x k + d k * y k
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c x => g61c_ext fun k => by
        show d k * (c • x) k = c • (d k * x k)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring }
    1 fun x => by
      rw [one_mul]
      refine lp.norm_mono (by norm_num) fun k => ?_
      show ‖d k * x k‖ ≤ ‖x k‖
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hd k)

theorem g61c_diag_apply (d : ℕ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) (x : g61c_L) (k : ℕ) :
    g61c_diag d hd x k = d k * x k := rfl

theorem g61c_bdd (d : ℕ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) : Bounded (g61c_Phi d) := by
  refine ⟨g61c_diag d hd, ?_⟩
  ext ⟨x, y⟩
  constructor
  · intro h; exact g61c_ext fun k => h k
  · intro h k; rw [h]; rfl

theorem g61c_proto : Proto g61c_Phi := by
  refine ⟨⟨⟨trivial, fun _ _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => trivial⟩, trivial⟩,
    fun f _ => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun f _ g _ => ⟨?_, ?_⟩⟩
  · have : g61c_Phi f = ⋂ k, {p : g61c_L × g61c_L | p.2 k = f k * p.1 k} := by
      ext p; simp [g61c_Phi]
    rw [this]
    have hc : ∀ k, Continuous (fun x : g61c_L => x k) :=
      fun k => (lp.lipschitzWith_one_eval 2 k).continuous
    exact isClosed_iInter fun k => isClosed_eq ((hc k).comp continuous_snd)
      (continuous_const.mul ((hc k).comp continuous_fst))
  · intro k; simp
  · intro x y z w h1 h2 k
    show (y + w) k = f k * (x + z) k
    rw [lp.coeFn_add, lp.coeFn_add, Pi.add_apply, Pi.add_apply, h1 k, h2 k, mul_add]
  · intro c x y h k
    show (c • y) k = f k * (c • x) k
    rw [lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      h k]; ring
  · intro x y z h1 h2; exact g61c_ext fun k => by rw [h1 k, h2 k]
  · ext ⟨x, y⟩
    constructor
    · intro h; exact g61c_ext fun k => by rw [h k, Pi.one_apply, one_mul]
    · intro h k; change y = x at h; show y k = 1 * x k; rw [h, one_mul]
  · rintro c f _ ⟨x, s⟩ ⟨y, hy, rfl⟩ k
    show (c • y) k = (c • f) k * x k
    rw [lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hy k]; ring
  · rintro f _ g _ ⟨x, s⟩ ⟨y, z, hy, hz, rfl⟩ k
    show (y + z) k = (f + g) k * x k
    rw [lp.coeFn_add, Pi.add_apply, Pi.add_apply, hy k, hz k]; ring
  · rintro ⟨x, w⟩ ⟨y, hy, hw⟩ k
    show w k = (f * g) k * x k
    rw [hw k, hy k, Pi.mul_apply]; ring
  · ext x
    constructor
    · rintro ⟨w, y, hy, hw⟩
      exact ⟨⟨y, hy⟩, ⟨w, fun k => by
        show w k = (f * g) k * x k
        rw [hw k, hy k, Pi.mul_apply]; ring⟩⟩
    · rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
      refine ⟨w, y, hy, fun k => ?_⟩
      show w k = f k * y k
      have := hw k
      simp only at this
      rw [this, hy k, Pi.mul_apply]; ring

def g61c_f0 : ℕ → ℂ := fun k => (k : ℂ) + 1
def g61c_g0 : ℕ → ℂ := fun k => 1 / ((k : ℂ) + 1)

theorem g61c_ne (k : ℕ) : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k

theorem g61c_g0_le (k : ℕ) : ‖g61c_g0 k‖ ≤ 1 := by
  unfold g61c_g0
  rw [norm_div, norm_one, show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  rw [div_le_one (by positivity)]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

theorem g61c_gf : g61c_g0 * g61c_f0 = 1 := by
  funext k; simp only [Pi.mul_apply, Pi.one_apply, g61c_g0, g61c_f0]
  field_simp [g61c_ne k]

theorem g61c_one_le (k : ℕ) : ‖(1 : ℕ → ℂ) k‖ ≤ 1 := by simp

theorem g61c_unbdd : ¬ Bounded (g61c_Phi g61c_f0) := by
  rintro ⟨T, hT⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ‖T‖
  set x : g61c_L := lp.single 2 n (1 : ℂ)
  have hx : (x, T x) ∈ g61c_Phi g61c_f0 := by rw [hT]; rfl
  have h1 := hx n
  simp only [x, lp.single_apply_self, mul_one, g61c_f0] at h1
  have h2 : ‖T x n‖ ≤ ‖T‖ := by
    calc ‖T x n‖ ≤ ‖T x‖ := lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ = ‖T‖ := by rw [lp.norm_single (by norm_num), norm_one, mul_one]
  rw [h1, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast] at h2
  push_cast at h2
  linarith

theorem solution : ¬ (∀ {F : Type} [Ring F] [Algebra ℂ F] {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi)
    (f : F) (M E : Set F) (hM : M ⊆ boundedElements Phi)
    (hE : E ⊆ boundedElements Phi) (hdet : Determines Phi M f)
    (hcriterion : AnchoredSet Phi E M ∨
      ∀ g ∈ M, ∃ N : Set F, AnchorSet Phi N ∧
        setProduct N {g} ⊆ setProduct (leftMultipliers Phi E) E),
    Determines Phi E f) := by
  intro h
  have hb1 : Bounded (g61c_Phi 1) := g61c_bdd 1 g61c_one_le
  have hbg : Bounded (g61c_Phi g61c_g0) := g61c_bdd _ g61c_g0_le
  have hbgf : Bounded (g61c_Phi (g61c_g0 * g61c_f0)) := by rw [g61c_gf]; exact hb1
  have hdet : Determines g61c_Phi {g61c_g0} g61c_f0 := by
    refine ⟨Set.singleton_subset_iff.2 hbg, fun x y => ⟨?_, ?_⟩⟩
    · intro hxy e he
      rw [show e = g61c_g0 from he.1]
      refine ⟨g61c_diag _ g61c_g0_le y, fun k => ?_, fun k => rfl⟩
      show g61c_g0 k * y k = (g61c_g0 * g61c_f0) k * x k
      rw [hxy k, Pi.mul_apply]; ring
    · intro H k
      obtain ⟨z, h1, h2⟩ := H g61c_g0 ⟨rfl, hbg, hbgf⟩
      have a := h1 k
      have b := h2 k
      simp only at a b
      rw [g61c_gf, Pi.one_apply, one_mul] at a
      rw [a] at b
      show y k = g61c_f0 k * x k
      rw [b]; simp only [g61c_g0, g61c_f0]
      field_simp [g61c_ne k]
  have hcrit : ∀ g ∈ ({g61c_g0} : Set (ℕ → ℂ)), ∃ N : Set (ℕ → ℂ), AnchorSet g61c_Phi N ∧
      setProduct N {g} ⊆ setProduct (leftMultipliers g61c_Phi {1}) {1} := by
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    refine ⟨{1}, ⟨Set.singleton_nonempty _, Set.singleton_subset_iff.2 hb1, fun x hx => ?_⟩, ?_⟩
    · have := hx 1 rfl
      exact g61c_ext fun k => by
        have h := this k
        simp only [Pi.one_apply, one_mul] at h
        rw [← h]
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      rw [Set.mem_singleton_iff] at ha hb
      subst ha; subst hb
      refine ⟨g61c_g0, fun e he => ?_, 1, rfl, by rw [one_mul, mul_one]⟩
      rw [Set.mem_singleton_iff] at he; subst he
      show Bounded (g61c_Phi (g61c_g0 * 1)); rw [mul_one]; exact hbg
  have hres := @h (ℕ → ℂ) _ _ g61c_L _ _ _ _ g61c_Phi g61c_proto g61c_f0 {g61c_g0} {1}
    (Set.singleton_subset_iff.2 hbg) (Set.singleton_subset_iff.2 hb1) hdet (Or.inr hcrit)
  have h0 : ((0 : g61c_L), lp.single 2 0 (1 : ℂ)) ∈ g61c_Phi g61c_f0 :=
    (hres.2 0 _).2 fun e he => by
      exfalso
      have hb := he.2.2
      rw [show e = 1 from he.1, one_mul] at hb
      exact g61c_unbdd hb
  have := h0 0
  simp at this
