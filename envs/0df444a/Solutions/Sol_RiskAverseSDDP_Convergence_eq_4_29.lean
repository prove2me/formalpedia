-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.eq_4_29
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:19:01.526777+00:00
-- url     : https://prove2.me/submissions/7afb79ba-649b-4143-9196-9d7847d8ccbc

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Definitions.Def_RiskAverseSDDP_Convergence_Sampling
import Theorems.Thm_RiskAverseSDDP_Convergence_proposition_3_1
import Theorems.Thm_RiskAverseSDDP_Convergence_lemma_3_5
open Filter Topology MeasureTheory ProbabilityTheory

namespace RASDDPEq429
open RiskAverseSDDP.Convergence

lemma mul_add_coe {w : ℝ} (hw : 0 ≤ w) (z : EReal) (c : ℝ) :
    (w : EReal) * (z + (c : EReal)) = (w : EReal) * z + ((w * c : ℝ) : EReal) := by
  rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hw) (EReal.coe_ne_top w),
    EReal.coe_mul]

lemma sum_add_coe {M : ℕ} (a : Fin M → EReal) (b : Fin M → ℝ) :
    ∑ j, (a j + ((b j : ℝ) : EReal)) = (∑ j, a j) + ((∑ j, b j : ℝ) : EReal) := by
  rw [Finset.sum_add_distrib]
  congr 1
  induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

lemma stageVal_mono {T n M q p : ℕ} (D : Model T n M q p) (s : ℕ) (j : Fin M)
    {V W : Hist n (s + 1) → EReal} (h : ∀ y, V y ≤ W y) (x : Hist n s) :
    D.stageVal s j V x ≤ D.stageVal s j W x := by
  unfold Model.stageVal
  exact iInf₂_mono fun y _ => add_le_add_right (h _) _

lemma Q_last {T n M q p : ℕ} (D : Model T n M q p) (x : Hist n T) : D.Q T x = 0 := by
  simp [Model.Q, Model.Qaux]

lemma Q_succ {T n M q p : ℕ} (D : Model T n M q p) (s : ℕ) (hs : s + 2 ≤ T)
    (x : Hist n (s + 1)) :
    D.Q (s + 1) x = D.rho (s + 2) (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) x) := by
  have h : T - (s + 1) = (T - (s + 2)) + 1 := by omega
  rw [Model.Q, h, Model.Qaux]
  rfl

/-- Validity of cuts: `𝒬^k_h ≤ 𝒬_h` everywhere. -/
lemma valid {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (hS : D.Standing) (R : Rules n M)
    (ys : ℕ → ℕ → Fin M) (r : RunData n M) (hr : D.IsRun R ys r) :
    ∀ d h, h + d = T → 1 ≤ h → ∀ k y, r.Qm k h y ≤ D.Q h y := by
  obtain ⟨hQ0, hQT, _, hcut⟩ := hr
  intro d
  induction d with
  | zero =>
    intro h hh _ k y
    have hh' : h = T := by omega
    subst hh'
    rw [hQT k, Q_last]
  | succ d ih =>
    intro h hh h1 k y
    obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
    have hs : s + 2 ≤ T := by omega
    have ih' := ih (s + 2) (by omega) (by omega)
    induction k generalizing y with
    | zero => rw [hQ0 (s + 1) h1 (by omega)]; exact bot_le
    | succ k ihk =>
      obtain ⟨hpk, _, hπ, hθ, hβ, hupd⟩ := hcut k s hs
      rw [hupd]
      refine max_le (ihk y) ?_
      set xt := r.hist (k + 1) s (sampNode ys (k + 1) s)
      set Z : Fin M → EReal := fun j => D.stageVal (s + 1) j (r.Qm k (s + 2)) xt
      set pk := R.pRule (s + 2) Z
      set d' := y - xt
      have hw : ∀ j, 0 ≤ pk j * D.Φ (s + 2) j := by
        intro j
        have hS' := hS (s + 2) (by omega) hs
        exact mul_nonneg ((hS'.2.2.1 hpk).1 j) (hS'.1 j).le
      have hinner : inner ℝ (r.β (k + 1) s) d' =
          ∑ j, (pk j * D.Φ (s + 2) j) * inner ℝ (r.π (k + 1) s j) d' := by
        rw [hβ, sum_inner]
        simp only [real_inner_smul_left]
      have hsub : ∀ j, Z j + ((inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal) ≤
          D.stageVal (s + 1) j (D.Q (s + 2)) y := by
        intro j
        exact ((hπ j).2 y).trans (stageVal_mono D (s + 1) j (ih' k) _)
      calc r.θ (k + 1) s + ((inner ℝ (r.β (k + 1) s) d' : ℝ) : EReal)
          = ∑ j, (((pk j * D.Φ (s + 2) j : ℝ) : EReal) * Z j +
              (((pk j * D.Φ (s + 2) j) * inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal)) := by
            rw [sum_add_coe, hθ, hinner]; rfl
        _ = ∑ j, ((pk j * D.Φ (s + 2) j : ℝ) : EReal) *
              (Z j + ((inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_add_coe (hw j)]
        _ ≤ ∑ j, ((pk j * D.Φ (s + 2) j : ℝ) : EReal) * D.stageVal (s + 1) j (D.Q (s + 2)) y := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left (hsub j) (by exact_mod_cast hw j)
        _ = D.wsum (s + 2) pk (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y) := rfl
        _ ≤ D.rho (s + 2) (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y) := by
            unfold Model.rho
            exact le_iSup₂ (f := fun π _ => D.wsum (s + 2) π
              (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y)) pk hpk
        _ = D.Q (s + 1) y := (Q_succ D s hs y).symm

lemma snoc_mem_prodSet {T n M q p s : ℕ} (D : Model T n M q p) {x : Hist n s}
    {y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ D.prodSet s) (hy : y ∈ D.Xc (s + 1)) :
    x.snoc y ∈ D.prodSet (s + 1) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Hist.snoc, PiLp.toLp_apply, Fin.snoc_last, Fin.val_last]; exact hy
  · simp only [Hist.snoc, PiLp.toLp_apply, Fin.snoc_castSucc, Fin.val_castSucc]; exact hx j

lemma hist_mem {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (R : Rules n M)
    (ys : ℕ → ℕ → Fin M) (r : RunData n M) (hr : D.IsRun R ys r) (k : ℕ) :
    ∀ s, s < T → ∀ ν : Fin s → Fin M, r.hist (k + 1) s ν ∈ D.prodSet (s + 1) := by
  intro s
  induction s with
  | zero =>
    intro hs ν
    have h := (hr.2.2.1 k 0 ν hs).2.1
    exact snoc_mem_prodSet D (fun i => Fin.elim0 i) h.1
  | succ s ih =>
    intro hs ν
    have h := (hr.2.2.1 k (s + 1) ν hs).2.1
    exact snoc_mem_prodSet D (ih (by omega) (Fin.init ν)) h.1

lemma prodSet_compact {T n M q p : ℕ} (D : Model T n M q p) (h : ℕ)
    (hc : ∀ i, i < h → IsCompact (D.Xc (i + 1))) : IsCompact (D.prodSet h) := by
  have hEq : D.prodSet h =
      WithLp.toLp 2 '' Set.univ.pi (fun i : Fin h => D.Xc (i.val + 1)) := by
    ext z
    constructor
    · intro hz
      exact ⟨WithLp.ofLp z, fun i _ => hz i, by simp⟩
    · rintro ⟨w, hw, rfl⟩ i
      exact hw i (Set.mem_univ _)
  rw [hEq]
  exact (isCompact_univ_pi fun i : Fin h => hc i.val i.isLt).image (PiLp.continuous_toLp 2 _)

lemma Qm_mono {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (R : Rules n M)
    (ys : ℕ → ℕ → Fin M) (r : RunData n M) (hr : D.IsRun R ys r)
    (s : ℕ) (hs : s + 2 ≤ T) {i j : ℕ} (hij : i ≤ j) (y : Hist n (s + 1)) :
    r.Qm i (s + 1) y ≤ r.Qm j (s + 1) y := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    obtain ⟨-, -, -, -, -, hupd⟩ := hr.2.2.2 _ s hs
    rw [hupd]
    exact le_max_left _ _

lemma ereal_fin_sub {a b : EReal} (ha : a ≠ ⊤) (ha' : a ≠ ⊥) (hb : b ≠ ⊤) (hb' : b ≠ ⊥) :
    a - b = ((a.toReal - b.toReal : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_toReal ha ha', EReal.coe_toReal hb hb']

/-- Deterministic step: if `f(x_k) - F_{k+1}(x_k) → 0` along `S`, then for every `η > 0`,
`{k ∈ S : f(x_k) - F_k(x_k) ≥ η}` is finite. -/
lemma step1 {E : Type*} [NormedAddCommGroup E] (K : Set E) (hK : IsCompact K) (x : ℕ → E)
    (hx : ∀ k, x k ∈ K) (f : E → EReal) (F : ℕ → E → EReal)
    (hf : ∀ y ∈ K, f y ≠ ⊥ ∧ f y ≠ ⊤)
    (hfc : ContinuousOn (fun y => (f y).toReal) K)
    (k0 : ℕ) (L : ℝ)
    (hF : ∀ k, k0 ≤ k → ∀ y z, F k y ≠ ⊥ ∧ F k y ≠ ⊤ ∧
      |(F k y).toReal - (F k z).toReal| ≤ L * ‖y - z‖)
    (hmono : ∀ i j, i ≤ j → ∀ y, F i y ≤ F j y)
    (S : Set ℕ)
    (hg : Tendsto (fun k => f (x k) - F (k + 1) (x k)) (atTop ⊓ 𝓟 S) (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    {k | (η : EReal) ≤ f (x k) - F k (x k) ∧ k ∈ S}.Finite := by
  by_contra hinf
  let pr : ℕ → Prop := fun k => (η : EReal) ≤ f (x k) - F k (x k) ∧ k ∈ S
  have hinf' : (Set.ofPred pr).Infinite := hinf
  have hφ : StrictMono (Nat.nth pr) := Nat.nth_strictMono hinf'
  have hφI : ∀ i, pr (Nat.nth pr i) := Nat.nth_mem_of_infinite hinf'
  obtain ⟨a, haK, ψ, hψ, hlim⟩ := hK.tendsto_subseq (fun i => hx (Nat.nth pr i))
  set c : ℕ → ℕ := fun i => Nat.nth pr (ψ i) with hcdef
  have hc : StrictMono c := hφ.comp hψ
  have hlim_within : Tendsto (fun i => x (c i)) atTop (𝓝[K] a) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlim
      (Eventually.of_forall fun i => hx (c i))
  have hflim : Tendsto (fun i => (f (x (c i))).toReal) atTop (𝓝 (f a).toReal) :=
    (hfc.continuousWithinAt haK).tendsto.comp hlim_within
  set δ := η / (3 * (|L| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have h0 : ∀ᶠ i in atTop, k0 ≤ c i := hc.tendsto_atTop.eventually (eventually_ge_atTop k0)
  have h1 : ∀ᶠ i in atTop, dist (x (c i)) a < δ / 2 :=
    (Metric.tendsto_nhds.1 hlim) _ (by positivity)
  have h2 : ∀ᶠ i in atTop, dist (f (x (c i))).toReal (f a).toReal < η / 6 :=
    (Metric.tendsto_nhds.1 hflim) _ (by positivity)
  have h3 : ∀ᶠ i in atTop, f (x (c i)) - F (c i + 1) (x (c i)) < ((η / 3 : ℝ) : EReal) := by
    have h := (tendsto_order.1 hg).2 ((η / 3 : ℝ) : EReal)
      (by exact_mod_cast (by positivity : (0 : ℝ) < η / 3))
    rw [eventually_inf_principal] at h
    have h' := hc.tendsto_atTop.eventually h
    filter_upwards [h'] with i hi using hi (hφI (ψ i)).2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (((h0.and h1).and h2).and h3)
  obtain ⟨⟨⟨hk0, hd1⟩, hfa1⟩, hg1⟩ := hN N le_rfl
  obtain ⟨⟨⟨-, hd2⟩, hfa2⟩, -⟩ := hN (N + 1) (by omega)
  have hlt : c N < c (N + 1) := hc (by omega)
  have hbad := (hφI (ψ (N + 1))).1
  set k1 := c N
  set k2 := c (N + 1)
  set x1 := x k1
  set x2 := x k2
  have hx1 : x1 ∈ K := hx k1
  have hx2 : x2 ∈ K := hx k2
  have hdist : ‖x1 - x2‖ < δ := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_right x1 x2 a]
  have hfdiff : (f x2).toReal - (f x1).toReal < η / 3 := by
    rw [Real.dist_eq] at hfa1 hfa2
    linarith [(abs_lt.1 hfa1).1, (abs_lt.1 hfa2).2]
  obtain ⟨hf1b, hf1t⟩ := hf x1 hx1
  obtain ⟨hf2b, hf2t⟩ := hf x2 hx2
  obtain ⟨hb1, hb1t, hlip⟩ := hF (k1 + 1) (by omega) x1 x2
  obtain ⟨hb2, hb2t, -⟩ := hF (k1 + 1) (by omega) x2 x1
  obtain ⟨hc2b, hc2t, -⟩ := hF k2 (by omega) x2 x1
  have hmon : F (k1 + 1) x2 ≤ F k2 x2 := hmono _ _ (by omega) x2
  have hmon' := EReal.toReal_le_toReal hmon hb2 hc2t
  rw [ereal_fin_sub hf1t hf1b hb1t hb1, EReal.coe_lt_coe_iff] at hg1
  rw [ereal_fin_sub hf2t hf2b hc2t hc2b, EReal.coe_le_coe_iff] at hbad
  have hlip' := abs_le.1 hlip
  have e1 : L * ‖x1 - x2‖ ≤ |L| * δ :=
    (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hdist.le (abs_nonneg L))
  have e2 : |L| * δ < η / 3 := by
    rw [hδdef, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg L]
  linarith

/-- Determinism of the forward pass: `hist (k + 1)` depends only on `Qm k`. -/
lemma hist_eq_of_Qm_eq {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (R : Rules n M)
    (ys ys' : ℕ → ℕ → Fin M) (r r' : RunData n M)
    (hr : D.IsRun R ys r) (hr' : D.IsRun R ys' r') (k : ℕ)
    (hQ : ∀ h, 1 ≤ h → h ≤ T → r.Qm k h = r'.Qm k h) :
    ∀ s, s < T → ∀ ν : Fin s → Fin M, r.hist (k + 1) s ν = r'.hist (k + 1) s ν := by
  intro s
  induction s with
  | zero =>
    intro hs ν
    have hx := (hr.2.2.1 k 0 ν hs).1
    have hx' := (hr'.2.2.1 k 0 ν hs).1
    have hq1 : r.Qm k 1 = r'.Qm k 1 := hQ 1 le_rfl (by omega)
    simp only [RunData.hist, RunData.phist] at hx hx' ⊢
    rw [hx, hx', hq1]
  | succ s ih =>
    intro hs ν
    have hprev : r.hist (k + 1) s (Fin.init ν) = r'.hist (k + 1) s (Fin.init ν) :=
      ih (by omega) (Fin.init ν)
    have hx := (hr.2.2.1 k (s + 1) ν hs).1
    have hx' := (hr'.2.2.1 k (s + 1) ν hs).1
    have hq : r.Qm k (s + 2) = r'.Qm k (s + 2) := hQ (s + 2) (by omega) (by omega)
    simp only [RunData.hist, RunData.phist] at hx hx' ⊢
    rw [hprev, hx, hx', hprev, hq]

/-- Determinism of one cut update: `Qm (k + 1)` depends only on `Qm k` and `ys (k + 1)`. -/
lemma Qm_succ_eq {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (R : Rules n M)
    (ys ys' : ℕ → ℕ → Fin M) (r r' : RunData n M)
    (hr : D.IsRun R ys r) (hr' : D.IsRun R ys' r') (k : ℕ)
    (hQ : ∀ h, 1 ≤ h → h ≤ T → r.Qm k h = r'.Qm k h)
    (hy : ∀ t, 2 ≤ t → t ≤ T → ys (k + 1) t = ys' (k + 1) t) :
    ∀ h, 1 ≤ h → h ≤ T → r.Qm (k + 1) h = r'.Qm (k + 1) h := by
  have hhist := hist_eq_of_Qm_eq D R ys ys' r r' hr hr' k hQ
  intro h h1 hT
  rcases eq_or_lt_of_le hT with rfl | hlt
  · rw [hr.2.1, hr'.2.1]
  · obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
    have hs : s + 2 ≤ T := by omega
    obtain ⟨-, -, hπ, hθ, hβ, hupd⟩ := hr.2.2.2 k s hs
    obtain ⟨-, -, hπ', hθ', hβ', hupd'⟩ := hr'.2.2.2 k s hs
    have hsamp : sampNode ys (k + 1) s = sampNode ys' (k + 1) s := by
      funext i
      exact hy (i.val + 2) (by omega) (by omega)
    have hxt : r.hist (k + 1) s (sampNode ys (k + 1) s) =
        r'.hist (k + 1) s (sampNode ys' (k + 1) s) := by
      rw [hsamp]
      exact hhist s (by omega) _
    have hq2 : r.Qm k (s + 2) = r'.Qm k (s + 2) := hQ (s + 2) (by omega) hs
    have hq1 : r.Qm k (s + 1) = r'.Qm k (s + 1) := hQ (s + 1) (by omega) (by omega)
    have hπeq : ∀ j, r.π (k + 1) s j = r'.π (k + 1) s j := by
      intro j
      rw [(hπ j).1, (hπ' j).1, hxt, hq2]
    have hθeq : r.θ (k + 1) s = r'.θ (k + 1) s := by
      rw [hθ, hθ', hxt, hq2]
    have hβeq : r.β (k + 1) s = r'.β (k + 1) s := by
      rw [hβ, hβ']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hxt, hq2, hπeq j]
    rw [hupd, hupd', hq1, hθeq, hβeq, hxt]

/-- `Qm k` depends only on the samples of iterations `1, …, k` and stages `2, …, T`. -/
lemma Qm_eq_of_agree {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (R : Rules n M)
    (ys ys' : ℕ → ℕ → Fin M) (r r' : RunData n M)
    (hr : D.IsRun R ys r) (hr' : D.IsRun R ys' r') (N : ℕ)
    (hag : ∀ k' t, 1 ≤ k' → k' ≤ N → 2 ≤ t → t ≤ T → ys k' t = ys' k' t) :
    ∀ k ≤ N, ∀ h, 1 ≤ h → h ≤ T → r.Qm k h = r'.Qm k h := by
  intro k hk
  induction k with
  | zero =>
    intro h h1 hT
    rcases eq_or_lt_of_le hT with rfl | hlt
    · rw [hr.2.1, hr'.2.1]
    · rw [hr.1 h h1 hlt, hr'.1 h h1 hlt]
  | succ k ih =>
    exact Qm_succ_eq D R ys ys' r r' hr hr' k (ih (by omega))
      (fun t ht2 htT => hag (k + 1) t (by omega) hk ht2 htT)

/-- The filtration σ-algebra `𝒢_k = σ(ξ^{k'}_{t'} : 1 ≤ k' ≤ k + 1, 2 ≤ t' ≤ T)`. -/
abbrev Gsigma (T M : ℕ) {Ω : Type*} (ξ : ℕ → Ω → ℕ → Fin M) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ k', ⨆ t', ⨆ (_ : 1 ≤ k' ∧ k' ≤ k + 1 ∧ 2 ≤ t' ∧ t' ≤ T),
    MeasurableSpace.comap (fun ω => ξ k' ω t') inferInstance

lemma Gsigma_mono (T M : ℕ) {Ω : Type*} (ξ : ℕ → Ω → ℕ → Fin M) :
    Monotone (Gsigma T M ξ) := by
  intro a b hab
  refine iSup_mono fun k' => iSup_mono fun t' => iSup_mono' fun h => ?_
  exact ⟨⟨h.1, h.2.1.trans (Nat.add_le_add_right hab 1), h.2.2.1, h.2.2.2⟩, le_rfl⟩

lemma Gsigma_le {T n M q p : ℕ} (D : Model T n M q p) {Ω : Type*} [m0 : MeasurableSpace Ω]
    (P : Measure Ω) (ξ : ℕ → Ω → ℕ → Fin M) (hH3 : D.H3 P ξ) (k : ℕ) :
    Gsigma T M ξ k ≤ m0 := by
  refine iSup_le fun k' => iSup_le fun t' => iSup_le fun h => ?_
  exact (hH3.1 k' t' h.1 h.2.2.1 h.2.2.2).comap_le

lemma measurableSet_Gsigma_of_depends (T M : ℕ) {Ω : Type*} (ξ : ℕ → Ω → ℕ → Fin M) (k : ℕ)
    (S : Set Ω)
    (hS : ∀ ω ω', (∀ k' t', 1 ≤ k' → k' ≤ k + 1 → 2 ≤ t' → t' ≤ T → ξ k' ω t' = ξ k' ω' t') →
      ω ∈ S → ω' ∈ S) :
    MeasurableSet[Gsigma T M ξ k] S := by
  let Φ : Ω → (Fin (k + 1) → Fin (T - 1) → Fin M) :=
    fun ω i j => ξ (i.val + 1) ω (j.val + 2)
  have hΦ : Measurable[Gsigma T M ξ k] Φ := by
    refine @measurable_pi_lambda Ω (Fin (k + 1)) (fun _ => Fin (T - 1) → Fin M)
      (Gsigma T M ξ k) _ Φ fun i => ?_
    refine @measurable_pi_lambda Ω (Fin (T - 1)) (fun _ => Fin M)
      (Gsigma T M ξ k) _ (fun ω j => Φ ω i j) fun j => ?_
    refine (comap_measurable (fun ω => ξ (i.val + 1) ω (j.val + 2))).mono ?_ le_rfl
    have hcond : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ k + 1 ∧ 2 ≤ j.val + 2 ∧ j.val + 2 ≤ T :=
      ⟨by omega, by omega, by omega, by omega⟩
    exact le_iSup_of_le (i.val + 1) (le_iSup_of_le (j.val + 2) (le_iSup_of_le hcond le_rfl))
  have hSeq : S = Φ ⁻¹' (Φ '' S) := by
    ext ω
    constructor
    · intro h; exact ⟨ω, h, rfl⟩
    · rintro ⟨ω', h', he⟩
      refine hS ω' ω (fun k' t' hk1 hkk ht2 htT => ?_) h'
      have h1 : k' - 1 < k + 1 := by omega
      have h2 : t' - 2 < T - 1 := by omega
      have hval := congrFun (congrFun he ⟨k' - 1, h1⟩) ⟨t' - 2, h2⟩
      simp only [Φ] at hval
      rwa [show k' - 1 + 1 = k' by omega, show t' - 2 + 2 = t' by omega] at hval
  rw [hSeq]
  exact hΦ (Set.toFinite _).measurableSet

/-- Independence and probability of sampling node `ν` at iteration `k + 2` given `𝒢_k`. -/
lemma measure_inter_sampNode_eq {T n M q p : ℕ} (D : Model T n M q p) (hS : D.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ : ℕ → Ω → ℕ → Fin M) (hH3 : D.H3 P ξ)
    (s : ℕ) (hs : s + 2 ≤ T) (ν : Fin s → Fin M) (k : ℕ)
    (S : Set Ω) (hS_m : MeasurableSet[Gsigma T M ξ k] S) :
    P (S ∩ {ω | sampNode (fun m t => ξ m ω t) (k + 2) s = ν}) =
      P S * ENNReal.ofReal (∏ i : Fin s, D.Φ (i.val + 2) (ν i)) := by
  suffices ∀ r (hr : r ≤ s),
      P (S ∩ {ω | ∀ i : Fin r, ξ (k + 2) ω (i.val + 2) = ν ⟨i.val, lt_of_lt_of_le i.isLt hr⟩}) =
        P S * ENNReal.ofReal (∏ i : Fin r, D.Φ (i.val + 2) (ν ⟨i.val, lt_of_lt_of_le i.isLt hr⟩)) by
    simpa [sampNode, funext_iff] using this s le_rfl
  intro r
  induction r with
  | zero =>
    intro _
    simp
  | succ r ih =>
    intro hr
    set Er : Set Ω :=
      {ω | ∀ i : Fin r, ξ (k + 2) ω (i.val + 2) = ν ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩}
    set Tr : Set Ω := {ω | ξ (k + 2) ω (r + 2) = ν ⟨r, hr⟩}
    have hsplit : {ω | ∀ i : Fin (r + 1),
        ξ (k + 2) ω (i.val + 2) = ν ⟨i.val, lt_of_lt_of_le i.isLt hr⟩} = Er ∩ Tr := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Er, Tr]
      constructor
      · intro h
        exact ⟨fun i => h i.castSucc, h (Fin.last r)⟩
      · rintro ⟨h1, h2⟩ i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using h2
        · simpa using h1 j
    set Past : MeasurableSpace Ω :=
      ⨆ k', ⨆ t', ⨆ (_ : 1 ≤ k' ∧ 2 ≤ t' ∧ t' ≤ T ∧ (k' < k + 2 ∨ (k' = k + 2 ∧ t' < r + 2))),
        MeasurableSpace.comap (fun ω => ξ k' ω t') inferInstance
    have hGP : Gsigma T M ξ k ≤ Past := by
      refine iSup_le fun k' => iSup_le fun t' => iSup_le fun h => ?_
      have hc : 1 ≤ k' ∧ 2 ≤ t' ∧ t' ≤ T ∧ (k' < k + 2 ∨ (k' = k + 2 ∧ t' < r + 2)) :=
        ⟨h.1, h.2.2.1, h.2.2.2, Or.inl (by omega)⟩
      exact le_iSup_of_le k' (le_iSup_of_le t' (le_iSup_of_le hc le_rfl))
    have hEr_m : MeasurableSet[Past] Er := by
      have hEr_eq : Er = ⋂ i : Fin r,
          (fun ω => ξ (k + 2) ω (i.val + 2)) ⁻¹' {ν ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩} := by
        ext ω; simp [Er]
      rw [hEr_eq]
      refine MeasurableSet.iInter fun i => ?_
      have hc : 1 ≤ k + 2 ∧ 2 ≤ i.val + 2 ∧ i.val + 2 ≤ T ∧
          (k + 2 < k + 2 ∨ (k + 2 = k + 2 ∧ i.val + 2 < r + 2)) :=
        ⟨by omega, by omega, by omega, Or.inr ⟨rfl, by omega⟩⟩
      have hle : MeasurableSpace.comap (fun ω => ξ (k + 2) ω (i.val + 2)) inferInstance ≤ Past :=
        le_iSup_of_le (k + 2) (le_iSup_of_le (i.val + 2) (le_iSup_of_le hc le_rfl))
      exact hle _ ⟨{ν ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩}, measurableSet_singleton _, rfl⟩
    have hTr_m : MeasurableSet[MeasurableSpace.comap (fun ω => ξ (k + 2) ω (r + 2)) inferInstance]
        Tr := ⟨{ν ⟨r, hr⟩}, measurableSet_singleton _, rfl⟩
    have hind := hH3.2.2 (k + 2) (r + 2) (by omega) (by omega) (by omega)
    have hmul : P (Tr ∩ (S ∩ Er)) = P Tr * P (S ∩ Er) :=
      ((ProbabilityTheory.Indep_iff _ _ P).1 hind) Tr (S ∩ Er) hTr_m ((hGP _ hS_m).inter hEr_m)
    have hPTr : P Tr = ENNReal.ofReal (D.Φ (r + 2) (ν ⟨r, hr⟩)) :=
      hH3.2.1 (k + 2) (r + 2) (ν ⟨r, hr⟩) (by omega) (by omega) (by omega)
    have hprod_nn : 0 ≤ ∏ i : Fin r, D.Φ (i.val + 2) (ν ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩) :=
      Finset.prod_nonneg fun i _ => (hS (i.val + 2) (by omega) (by omega)).1 _ |>.le
    have hset : S ∩ (Er ∩ Tr) = Tr ∩ (S ∩ Er) := by
      ext ω; simp [and_comm, and_left_comm]
    rw [hsplit, hset, hmul, hPTr, ih (by omega), Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ENNReal.ofReal_mul hprod_nn]
    ring

/-- Lévy's conditional Borel–Cantelli step for adapted events `A_k`, `B_k` with `A_{k+1} ∈ ℱ_k`
and conditional probability `q > 0` for `B_{k+1}` given `ℱ_k`. -/
lemma levy_step {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (A B : ℕ → Set Ω)
    (hA : ∀ k, MeasurableSet[ℱ k] (A k))
    (hA1 : ∀ k, MeasurableSet[ℱ k] (A (k + 1)))
    (hB : ∀ k, MeasurableSet[ℱ k] (B k))
    (q : ℝ) (hq : 0 < q)
    (hprod : ∀ k S, MeasurableSet[ℱ k] S → P (S ∩ B (k + 1)) = P S * ENNReal.ofReal q) :
    ∀ᵐ ω ∂P, {k | ω ∈ A k ∧ ω ∈ B k}.Finite → {k | ω ∈ A k}.Finite := by
  have hs : ∀ k, MeasurableSet[ℱ k] (A k ∩ B k) := fun k => (hA k).inter (hB k)
  have levy := ae_mem_limsup_atTop_iff (ℱ := ℱ) P hs
  have hce : ∀ k, P[(A (k + 1) ∩ B (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] =ᵐ[P]
      (A (k + 1)).indicator (fun _ => q) := by
    intro k
    refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le k)
      ((integrable_const (1 : ℝ)).indicator (ℱ.le (k + 1) _ (hs (k + 1))))
      (fun S _ _ => ((integrable_const q).indicator (ℱ.le k _ (hA1 k))).integrableOn)
      (fun S hSm _ => ?_)
      (stronglyMeasurable_const.indicator (hA1 k)).aestronglyMeasurable).symm
    have hA1m : MeasurableSet (A (k + 1)) := ℱ.le k _ (hA1 k)
    have hABm : MeasurableSet (A (k + 1) ∩ B (k + 1)) := ℱ.le (k + 1) _ (hs (k + 1))
    rw [integral_indicator_const q hA1m, measureReal_restrict_apply hA1m, smul_eq_mul]
    rw [integral_indicator_const (1 : ℝ) hABm, measureReal_restrict_apply hABm, smul_eq_mul, mul_one]
    have hEq1 : A (k + 1) ∩ S = S ∩ A (k + 1) := Set.inter_comm _ _
    have hEq2 : (A (k + 1) ∩ B (k + 1)) ∩ S = (S ∩ A (k + 1)) ∩ B (k + 1) := by
      ext ω; simp only [Set.mem_inter_iff]; tauto
    rw [hEq1, hEq2, Measure.real, Measure.real, hprod k (S ∩ A (k + 1)) (hSm.inter (hA1 k)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le]
  have hce' := ae_all_iff.2 hce
  filter_upwards [levy, hce'] with ω hl hc
  intro hfin
  by_contra hinfA
  have hinfA' : {k | ω ∈ A k}.Infinite := hinfA
  set u : ℕ → ℝ := fun N => ∑ k ∈ Finset.range N, (A (k + 1)).indicator (fun _ => q) ω with hu
  have hu_mono : Monotone u := by
    refine monotone_nat_of_le_succ fun N => ?_
    simp only [hu, Finset.sum_range_succ]
    have : 0 ≤ (A (N + 1)).indicator (fun _ => q) ω :=
      Set.indicator_nonneg (fun _ _ => hq.le) _
    linarith
  have hgrow : ∀ M : ℕ, ∃ N, (M : ℝ) * q ≤ u N := by
    intro M
    induction M with
    | zero => exact ⟨0, by simp [hu]⟩
    | succ M ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨k', hk'mem, hk'gt⟩ := hinfA'.exists_gt N
      obtain ⟨k, rfl⟩ : ∃ k, k' = k + 1 := ⟨k' - 1, by omega⟩
      refine ⟨k + 1, ?_⟩
      have e1 : u (k + 1) = u k + q := by
        simp only [hu, Finset.sum_range_succ]
        rw [Set.indicator_of_mem (show ω ∈ A (k + 1) from hk'mem)]
      have e2 : u N ≤ u k := hu_mono (by omega)
      push_cast
      linarith
  have hsum : Tendsto (fun N => ∑ k ∈ Finset.range N,
      P[(A (k + 1) ∩ B (k + 1)).indicator (1 : Ω → ℝ) | ℱ k] ω) atTop atTop := by
    simp_rw [hc]
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨M, hM⟩ := exists_nat_ge (b / q)
    obtain ⟨N, hN⟩ := hgrow M
    refine ⟨N, fun a ha => ?_⟩
    have h1 := hu_mono ha
    have h2 : b ≤ M * q := by rwa [div_le_iff₀ hq] at hM
    show b ≤ u a
    linarith
  have hmem := hl.2 hsum
  rw [mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite] at hmem
  exact hmem hfin

end RASDDPEq429

open RiskAverseSDDP.Convergence RASDDPEq429 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℕ → Fin M) (hH3 : D.H3 P ξ)
    (r : Ω → RunData n M) (hr : ∀ ω, D.IsRun R (fun k t => ξ k ω t) (r ω)) :
    ∀ s, s + 2 ≤ T → ∀ ν : Fin s → Fin M, ∀ᵐ ω ∂P,
      Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
        (atTop ⊓ 𝓟 (iterSet (fun k t => ξ k ω t) s ν)) (𝓝 0) →
      Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
        (atTop ⊓ 𝓟 {k | 1 ≤ k ∧ sampNode (fun k t => ξ k ω t) k s ≠ ν}) (𝓝 0) := by
  intro s hs ν
  have hε : 0 < ε := hH2.1
  have hprop := proposition_3_1 D ε hS hH2 (s + 1) (by omega) (by omega) (ε / 2)
    (by linarith) (by linarith)
  have hsub : D.prodSet (s + 1) ⊆ Metric.cthickening (ε / 2) (D.prodSet (s + 1)) :=
    Metric.self_subset_cthickening _
  have hQfin : ∀ x ∈ D.prodSet (s + 1), D.Q (s + 1) x ≠ ⊥ ∧ D.Q (s + 1) x ≠ ⊤ :=
    fun x hx => hprop.2.1 x (hsub hx)
  have hQcont : ContinuousOn (fun x => (D.Q (s + 1) x).toReal) (D.prodSet (s + 1)) :=
    hprop.2.2.mono hsub
  have hcompact : IsCompact (D.prodSet (s + 1)) :=
    prodSet_compact D (s + 1) fun i hi => (hH2.2 i (by omega)).1.2.2
  have hxmem : ∀ ω k, (r ω).hist (k + 1) s ν ∈ D.prodSet (s + 1) :=
    fun ω k => hist_mem D R _ (r ω) (hr ω) k s (by omega) ν
  -- Filtration and sampling probability q > 0
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    ⟨Gsigma T M ξ, Gsigma_mono T M ξ, Gsigma_le D P ξ hH3⟩
  set q : ℝ := ∏ i : Fin s, D.Φ (i.val + 2) (ν i) with hqdef
  have hq : 0 < q :=
    Finset.prod_pos fun i _ => (hS (i.val + 2) (by omega) (by omega)).1 (ν i)
  -- Probabilistic step via Lévy's conditional Borel–Cantelli for each η > 0
  have step2 : ∀ η : ℝ, 0 < η → ∀ᵐ ω ∂P,
      {k | ω ∈ {ω | (η : EReal) ≤ D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
            (r ω).Qm k (s + 1) ((r ω).hist (k + 1) s ν)} ∧
          ω ∈ {ω | sampNode (fun m t => ξ m ω t) (k + 1) s = ν}}.Finite →
      {k | ω ∈ {ω | (η : EReal) ≤ D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
            (r ω).Qm k (s + 1) ((r ω).hist (k + 1) s ν)}}.Finite := by
    intro η _
    refine levy_step P ℱ
      (fun k => {ω | (η : EReal) ≤ D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
        (r ω).Qm k (s + 1) ((r ω).hist (k + 1) s ν)})
      (fun k => {ω | sampNode (fun m t => ξ m ω t) (k + 1) s = ν})
      ?_ ?_ ?_ q hq ?_
    · intro k
      refine measurableSet_Gsigma_of_depends T M ξ k _ fun ω ω' hag hmem => ?_
      have hQ := Qm_eq_of_agree D R _ _ (r ω) (r ω') (hr ω) (hr ω') (k + 1) hag k (by omega)
      have hH := hist_eq_of_Qm_eq D R _ _ (r ω) (r ω') (hr ω) (hr ω') k hQ s (by omega) ν
      have hQs := hQ (s + 1) (by omega) (by omega)
      simp only [Set.mem_ofPred_eq] at hmem ⊢
      rwa [← hH, ← hQs]
    · intro k
      refine measurableSet_Gsigma_of_depends T M ξ k _ fun ω ω' hag hmem => ?_
      have hQ := Qm_eq_of_agree D R _ _ (r ω) (r ω') (hr ω) (hr ω') (k + 1) hag (k + 1) le_rfl
      have hH := hist_eq_of_Qm_eq D R _ _ (r ω) (r ω') (hr ω) (hr ω') (k + 1) hQ s (by omega) ν
      have hQs := hQ (s + 1) (by omega) (by omega)
      simp only [Set.mem_ofPred_eq] at hmem ⊢
      rwa [← hH, ← hQs]
    · intro k
      refine measurableSet_Gsigma_of_depends T M ξ k _ fun ω ω' hag hmem => ?_
      simp only [Set.mem_ofPred_eq] at hmem ⊢
      rw [← hmem]
      funext i
      exact (hag (k + 1) (i.val + 2) (by omega) le_rfl (by omega) (by omega)).symm
    · intro k S hSm
      exact measure_inter_sampNode_eq D hS P ξ hH3 s hs ν k S hSm
  have hall := ae_all_iff.2 fun j : ℕ => step2 (1 / ((j : ℝ) + 1)) (by positivity)
  filter_upwards [hall] with ω hfin hω
  -- Shift the hypothesis along `k ↦ k + 1`
  set S : Set ℕ := {k | sampNode (fun m t => ξ m ω t) (k + 1) s = ν}
  have hshift : Tendsto (fun k => k + 1) (atTop ⊓ 𝓟 S)
      (atTop ⊓ 𝓟 (iterSet (fun m t => ξ m ω t) s ν)) := by
    refine tendsto_inf.2 ⟨(tendsto_add_atTop_nat 1).mono_left inf_le_left, ?_⟩
    rw [tendsto_principal]
    filter_upwards [mem_inf_of_right (mem_principal_self S)] with k hk
    exact ⟨by omega, hk⟩
  have hg : Tendsto (fun k => D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
      (r ω).Qm (k + 1) (s + 1) ((r ω).hist (k + 1) s ν)) (atTop ⊓ 𝓟 S) (𝓝 0) :=
    hω.comp hshift
  -- Apply Lemma 3.5 for uniform Lipschitz continuity of `Qm k (s + 1)` for `k ≥ T`
  have h35 := lemma_3_5 D ε hS hH2 R (fun m t => ξ m ω t) (r ω) (hr ω)
  extract_lets L at h35
  have hF : ∀ k, T ≤ k → ∀ y z : Hist n (s + 1),
      (r ω).Qm k (s + 1) y ≠ ⊥ ∧ (r ω).Qm k (s + 1) y ≠ ⊤ ∧
      |((r ω).Qm k (s + 1) y).toReal - ((r ω).Qm k (s + 1) z).toReal| ≤ L.toReal * ‖y - z‖ :=
    fun k hk y z => (h35 (s + 1) (by omega) hs k (by omega)).2.2 y z
  -- Combine Step 1 and Step 2 for every η = 1 / (j + 1)
  have hFfin : ∀ j : ℕ, {k | ((1 / ((j : ℝ) + 1) : ℝ) : EReal) ≤
      D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
        (r ω).Qm k (s + 1) ((r ω).hist (k + 1) s ν)}.Finite := by
    intro j
    refine hfin j ?_
    exact step1 (D.prodSet (s + 1)) hcompact (fun k => (r ω).hist (k + 1) s ν) (hxmem ω)
      (D.Q (s + 1)) (fun k => (r ω).Qm k (s + 1)) hQfin hQcont T L.toReal hF
      (fun i j hij y => Qm_mono D R _ (r ω) (hr ω) s hs hij y) S hg
      (1 / ((j : ℝ) + 1)) (by positivity)
  -- Conclude full convergence along `atTop`, hence along the unselected iterations
  have hval := valid D hS R (fun m t => ξ m ω t) (r ω) (hr ω) (T - (s + 1)) (s + 1)
    (by omega) (by omega)
  have hnonneg : ∀ k, 0 ≤ D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
      (r ω).Qm (k + 1) (s + 1) ((r ω).hist (k + 1) s ν) := by
    intro k
    have hq' := hQfin _ (hxmem ω k)
    exact (EReal.sub_nonneg (Or.inl hq'.2) (Or.inl hq'.1)).2 (hval (k + 1) _)
  have hgh : ∀ k, D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
      (r ω).Qm (k + 1) (s + 1) ((r ω).hist (k + 1) s ν) ≤
      D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
      (r ω).Qm k (s + 1) ((r ω).hist (k + 1) s ν) :=
    fun k => EReal.sub_le_sub le_rfl (Qm_mono D R _ (r ω) (hr ω) s hs (Nat.le_succ k) _)
  have hall_lim : Tendsto (fun k => D.Q (s + 1) ((r ω).hist (k + 1) s ν) -
      (r ω).Qm (k + 1) (s + 1) ((r ω).hist (k + 1) s ν)) atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun k => lt_of_lt_of_le ha (hnonneg k)
    · intro a ha
      obtain ⟨η, hη0, hηa⟩ := EReal.lt_iff_exists_real_btwn.1 ha
      have hη0' : (0 : ℝ) < η := by exact_mod_cast hη0
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hη0'
      have hev := (hFfin j).eventually_cofinite_notMem
      rw [Nat.cofinite_eq_atTop] at hev
      filter_upwards [hev] with k hk
      simp only [not_le] at hk
      calc _ ≤ _ := hgh k
        _ < _ := hk
        _ < (η : EReal) := by exact_mod_cast hj
        _ < a := hηa
  have hfull : Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) -
      (r ω).Qm k (s + 1) ((r ω).hist k s ν)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).1 hall_lim
  exact hfull.mono_left inf_le_left
