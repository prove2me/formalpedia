-- Prove2me | solution 1 for SemilinearHJ.Verification.proposition_4_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:45:37.373507+00:00
-- url     : https://prove2.me/submissions/f6da1c14-9dff-4399-8db1-9bb016fd45a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting
import Theorems.Thm_SemilinearHJ_Verification_proposition_4_3
import Theorems.Thm_SemilinearHJ_Verification_eq_4_11

namespace HJSeg

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma combo_mem_intrinsicInterior {X : Set V} (hX : Convex ℝ X) {x z : V} (hx : x ∈ X)
    (hz : z ∈ intrinsicInterior ℝ X) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    (1 - l) • x + l • z ∈ intrinsicInterior ℝ X := by
  rw [mem_intrinsicInterior] at hz ⊢
  obtain ⟨z', hz', rfl⟩ := hz
  have hxA : x ∈ affineSpan ℝ X := subset_affineSpan ℝ X hx
  have hwA : (1 - l) • x + l • (z' : V) ∈ affineSpan ℝ X := by
    have := AffineMap.lineMap_mem (Q := affineSpan ℝ X) l hxA z'.2
    rwa [AffineMap.lineMap_apply_module] at this
  refine ⟨⟨_, hwA⟩, ?_, rfl⟩
  have hS : ((↑) ⁻¹' X : Set (affineSpan ℝ X)) ∈ nhds z' := mem_interior_iff_mem_nhds.1 hz'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨l * ε, mul_pos hl0 hε, fun q hq => ?_⟩
  have hqA : (q : V) ∈ affineSpan ℝ X := q.2
  -- p = x + l⁻¹ (q - x)
  have hpA : (1 - l⁻¹) • x + l⁻¹ • (q : V) ∈ affineSpan ℝ X := by
    have := AffineMap.lineMap_mem (Q := affineSpan ℝ X) l⁻¹ hxA hqA
    rwa [AffineMap.lineMap_apply_module] at this
  let p : affineSpan ℝ X := ⟨_, hpA⟩
  have hp : p ∈ Metric.ball z' ε := by
    rw [Metric.mem_ball, Subtype.dist_eq] at hq ⊢
    have hq' : dist (q : V) ((1 - l) • x + l • (z' : V)) < l * ε := hq
    have heq : ((1 - l⁻¹) • x + l⁻¹ • (q : V)) - (z' : V) =
        l⁻¹ • ((q : V) - ((1 - l) • x + l • (z' : V))) := by
      rw [smul_sub, smul_add, smul_smul, smul_smul, mul_sub, mul_one, inv_mul_cancel₀ hl0.ne']
      module
    show dist ((1 - l⁻¹) • x + l⁻¹ • (q : V)) (z' : V) < ε
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl0), ← dist_eq_norm]
    rw [inv_mul_lt_iff₀ hl0]
    exact hq'
  have hpX : ((1 - l⁻¹) • x + l⁻¹ • (q : V)) ∈ X := hball hp
  have hcomb := hX hx hpX (by linarith : (0:ℝ) ≤ 1 - l) hl0.le (by ring)
  have : (1 - l) • x + l • ((1 - l⁻¹) • x + l⁻¹ • (q : V)) = (q : V) := by
    rw [smul_add, smul_smul, smul_smul, mul_sub, mul_one, mul_inv_cancel₀ hl0.ne']
    module
  show (q : V) ∈ X
  rw [← this]; exact hcomb

end HJSeg


open SemilinearHJ.Verification Filter Topology
open scoped ENNReal MeasureTheory

namespace HJApprox

variable {n : ℕ}

/-- Shrink a path towards a point `z`. -/
def shrink (l : ℝ) (z : E n) (φ : ℝ → E n) : ℝ → E n := fun t => (1 - l) • φ t + l • z

lemma isPath_shrink {X : Set (E n)} (hconv : Convex ℝ X) {z : E n} (hz : z ∈ X) {l : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {T : ℝ} {φ : ℝ → E n} (h : IsPath X T φ) :
    IsPath X T (shrink l z φ) := by
  obtain ⟨hT, ⟨K, hK⟩, hmap⟩ := h
  refine ⟨hT, ⟨K, LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩, fun t ht => ?_⟩
  · simp only [shrink, dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l)]
    have := hK.dist_le_mul a ha b hb
    have h0 : 0 ≤ dist (φ a) (φ b) := dist_nonneg
    nlinarith
  · exact hconv (hmap ht) hz (by linarith) hl0 (by ring)

lemma derivWithin_shrink (l : ℝ) (z : E n) (φ : ℝ → E n) {T t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    derivWithin (shrink l z φ) (Set.Icc 0 T) t = (1 - l) • derivWithin φ (Set.Icc 0 T) t := by
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  have : shrink l z φ = fun t => ((1 - l) • φ) t + l • z := rfl
  rw [this, deriv_add_const, deriv_const_smul_field]

lemma runCost_shrink {X : Set (E n)} (Ψ : E n → E n) (r : ℝ) {K : NNReal}
    (hK : LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i) (hconv : Convex ℝ X)
    {z : E n} (hz : z ∈ X) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ x ∈ X, ‖z - x‖ ≤ D)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {x : E n} (hx : x ∈ X) (v : E n) :
    runCost X Ψ r ((1 - l) • x + l • z) ((1 - l) • v) ≤
      runCost X Ψ r x v + ENNReal.ofReal (l * K * D * r) := by
  unfold runCost
  by_cases h : v ∈ tanCone X x ∧ v ∈ ballR X r
  · obtain ⟨⟨y, hy, s, hs, hv⟩, hvb⟩ := h
    have hx' : (1 - l) • x + l • z ∈ X := hconv hx hz (by linarith) hl0 (by ring)
    have h1 : (1 - l) • v ∈ tanCone X ((1 - l) • x + l • z) := by
      refine ⟨(1 - l) • y + l • z, hconv hy hz (by linarith) hl0 (by ring), s, hs, ?_⟩
      rw [hv]; module
    have h2 : (1 - l) • v ∈ ballR X r := by
      refine ⟨Submodule.smul_mem _ _ hvb.1, ?_⟩
      have : l1 ((1 - l) • v) = (1 - l) * l1 v := by
        simp only [l1, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l),
          Finset.mul_sum]
      rw [this]
      have := hvb.2
      have hl1v : 0 ≤ l1 v := Finset.sum_nonneg fun i _ => abs_nonneg _
      nlinarith
    rw [if_pos ⟨h1, h2⟩, if_pos ⟨⟨y, hy, s, hs, hv⟩, hvb⟩]
    have hS0 : 0 ≤ ∑ i, Ψ x i * max (v i) 0 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hΨ0 x hx i) (le_max_right _ _)
    have hc0 : 0 ≤ l * K * D * r := by
      have : 0 ≤ r := le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) hvb.2
      have := K.2
      positivity
    rw [← ENNReal.ofReal_add hS0 hc0]
    apply ENNReal.ofReal_le_ofReal
    have hΨb : ∀ i, Ψ ((1 - l) • x + l • z) i ≤ Ψ x i + l * K * D := by
      intro i
      have h1 : |Ψ ((1 - l) • x + l • z) i - Ψ x i| ≤ ‖Ψ ((1 - l) • x + l • z) - Ψ x‖ := by
        have := PiLp.norm_apply_le (Ψ ((1 - l) • x + l • z) - Ψ x) i
        simpa [Real.norm_eq_abs] using this
      have h2 : ‖Ψ ((1 - l) • x + l • z) - Ψ x‖ ≤ K * ‖((1 - l) • x + l • z) - x‖ := by
        have := hK.dist_le_mul _ hx' _ hx
        simpa [dist_eq_norm] using this
      have h3 : ((1 - l) • x + l • z) - x = l • (z - x) := by module
      rw [h3, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0] at h2
      have h4 : (K : ℝ) * (l * ‖z - x‖) ≤ K * (l * D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD x hx) hl0) K.2
      have := (abs_le.1 h1).2
      nlinarith
    have hmax : ∀ i : Fin n, max (((1 - l) • v) i) 0 ≤ max (v i) 0 := by
      intro i
      simp only [PiLp.smul_apply, smul_eq_mul]
      rcases le_total 0 (v i) with hvi | hvi
      · exact max_le (le_trans (by nlinarith) (le_max_left _ _)) (le_max_right _ _)
      · exact max_le (le_trans (by nlinarith) (le_max_right _ _)) (le_max_right _ _)
    have hsum : ∑ i, max (v i) 0 ≤ r :=
      le_trans (Finset.sum_le_sum fun i _ => max_le (le_abs_self _) (abs_nonneg _)) hvb.2
    calc ∑ i, Ψ ((1 - l) • x + l • z) i * max (((1 - l) • v) i) 0
        ≤ ∑ i, (Ψ x i + l * K * D) * max (v i) 0 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul (hΨb i) (hmax i) (le_max_right _ _)
            (le_trans (hΨ0 _ hx' i) (hΨb i))
      _ = ∑ i, Ψ x i * max (v i) 0 + l * K * D * ∑ i, max (v i) 0 := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, Ψ x i * max (v i) 0 + l * K * D * r := by
          have : 0 ≤ l * K * D := by have := K.2; positivity
          nlinarith
  · rw [if_neg h, top_add]; exact le_top

lemma pathCost_shrink {X : Set (E n)} (Ψ : E n → E n) (r : ℝ) {K : NNReal}
    (hK : LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i) (hconv : Convex ℝ X)
    {z : E n} (hz : z ∈ X) {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ x ∈ X, ‖z - x‖ ≤ D)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {T : ℝ} {φ : ℝ → E n} (h : IsPath X T φ) :
    pathCost X Ψ r T (shrink l z φ) ≤
      pathCost X Ψ r T φ + ENNReal.ofReal (l * K * D * r) * ENNReal.ofReal T := by
  unfold pathCost
  rw [MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Icc.symm,
    MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Icc.symm]
  calc ∫⁻ t in Set.Ioo 0 T, runCost X Ψ r (shrink l z φ t) (derivWithin (shrink l z φ) (Set.Icc 0 T) t)
      ≤ ∫⁻ t in Set.Ioo 0 T, (runCost X Ψ r (φ t) (derivWithin φ (Set.Icc 0 T) t) +
          ENNReal.ofReal (l * K * D * r)) := by
        refine MeasureTheory.lintegral_mono_ae ((MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
          (Eventually.of_forall fun t ht => ?_))
        rw [derivWithin_shrink l z φ ht]
        exact runCost_shrink Ψ r hK hΨ0 hconv hz hD0 hD hl0 hl1
          (h.2.2 (Set.Ioo_subset_Icc_self ht)) _
    _ = (∫⁻ t in Set.Ioo 0 T, runCost X Ψ r (φ t) (derivWithin φ (Set.Icc 0 T) t)) +
          ENNReal.ofReal (l * K * D * r) * ENNReal.ofReal T := by
        rw [MeasureTheory.lintegral_add_right _ measurable_const, MeasureTheory.setLIntegral_const,
          Real.volume_Ioo, sub_zero]

end HJApprox

/-- `H(x, u) ≥ 0` at states where `Ψ(x) ≥ 0`: the choice `v = 0 ∈ TX ∩ B_r` gives value `0`. -/
lemma ham_nonneg_aux {n : ℕ} (X : Set (E n)) (Ψ : E n → E n) (r : ℝ) (hr : 0 < r) (x u : E n)
    (hΨx : ∀ i, 0 ≤ Ψ x i) : 0 ≤ ham X Ψ r x u := by
  unfold ham
  have h0 : (0 : E n) ∈ ballR X r := ⟨Submodule.zero_mem _, by simp [l1, hr.le]⟩
  have hbdd : BddAbove ((fun v => inner ℝ u v - ∑ i, Ψ x i * max (v i) 0) '' ballR X r) := by
    refine ⟨r * ∑ i, |u i|, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have hvi : ∀ i, |v i| ≤ r := fun i =>
      le_trans (Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)) hv.2
    have h1 : inner ℝ u v ≤ r * ∑ i, |u i| := by
      rw [PiLp.inner_apply, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [RCLike.inner_apply, conj_trivial]
      calc v i * u i ≤ |v i * u i| := le_abs_self _
        _ = |v i| * |u i| := abs_mul _ _
        _ ≤ r * |u i| := mul_le_mul_of_nonneg_right (hvi i) (abs_nonneg _)
    have h2 : 0 ≤ ∑ i, Ψ x i * max (v i) 0 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hΨx i) (le_max_right _ _)
    linarith
  refine le_trans ?_ (le_csSup hbdd ⟨0, h0, rfl⟩)
  simp


theorem solution {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty) :
    (∀ x ∈ X, srcVal X Ψ r X0 x ≠ ⊤) ∧
      IsMaxViscSol X Ψ r X0 (fun x => (srcVal X Ψ r X0 x).toReal) := by
  obtain ⟨hfin, hsub⟩ := proposition_4_3 X hX Ψ hΨL hΨ0 r hr X0 hX0c hX0X hX0
  have hsuper : IsViscSuper X Ψ r X0 (fun x => (srcVal X Ψ r X0 x).toReal) :=
    ⟨hsub.1, hsub.2.1, fun ϕ _ x0 hx0 _ => ham_nonneg_aux X Ψ r hr x0 _ (hΨ0 x0 hx0.1)⟩
  refine ⟨hfin, ⟨hsub, hsuper⟩, ?_⟩
  intro Vh hVh x hx
  obtain ⟨S, hSne, hXS⟩ := hX
  have hconv : Convex ℝ X := hXS ▸ convex_convexHull ℝ _
  have hXne : X.Nonempty := hXS ▸ (hSne.coe_sort).elim fun s => ⟨s, subset_convexHull ℝ _ s.2⟩
  have hXcpt : IsCompact X := by
    have : IsCompact (convexHull ℝ (S : Set (E n))) := S.finite_toSet.isCompact_convexHull ℝ
    rwa [← hXS] at this
  obtain ⟨z, hzI⟩ := hXne.intrinsicInterior hconv
  have hzX : z ∈ X := intrinsicInterior_subset hzI
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall z).1 hXcpt.isBounded
  set D := max R 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hD : ∀ y ∈ X, ‖z - y‖ ≤ D := fun y hy => by
    have := hR hy
    rw [Metric.mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub] at this
    exact le_trans this (le_max_left _ _)
  obtain ⟨K, hK⟩ := hΨL
  have hXP : IsPolytope X := ⟨S, hSne, hXS⟩
  have h411 := eq_4_11 X hXP Ψ ⟨K, hK⟩ hΨ0 r hr X0 hX0c hX0X Vh hVh
  rw [← ENNReal.ofReal_le_iff_le_toReal (hfin x hx)]
  unfold srcVal
  refine le_iInf fun T => le_iInf fun φ => le_iInf fun hφ => ?_
  obtain ⟨hp, h0, hT⟩ := hφ
  by_cases hc : pathCost X Ψ r T φ = ⊤
  · rw [hc]; exact le_top
  set c := (pathCost X Ψ r T φ).toReal with hcdef
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hc, ENNReal.ofReal_le_ofReal_iff hc0]
  set M := K * D * r * T with hM
  have hT0 : 0 ≤ T := hp.1
  have hφ0X : φ 0 ∈ X := hp.2.2 ⟨le_rfl, hT0⟩
  -- the key inequality for shrunk paths
  have key : ∀ l ∈ Set.Ioo (0:ℝ) 1,
      Vh ((1 - l) • x + l • z) - Vh ((1 - l) • φ 0 + l • z) ≤ c + l * M := by
    intro l hl
    have hxl := HJSeg.combo_mem_intrinsicInterior hconv hx hzI hl.1 hl.2.le
    have hyl := HJSeg.combo_mem_intrinsicInterior hconv hφ0X hzI hl.1 hl.2.le
    have h1 := h411 _ hxl _ hyl
    have hpl := HJApprox.isPath_shrink hconv hzX hl.1.le hl.2.le hp
    have h2 : minCost X Ψ r ((1 - l) • φ 0 + l • z) ((1 - l) • x + l • z) ≤
        pathCost X Ψ r T (HJApprox.shrink l z φ) := by
      unfold minCost
      refine iInf_le_of_le T (iInf_le_of_le (HJApprox.shrink l z φ) (iInf_le_of_le ⟨hpl, rfl, ?_⟩ le_rfl))
      simp [HJApprox.shrink, hT]
    have h3 := HJApprox.pathCost_shrink Ψ r hK hΨ0 hconv hzX hD0 hD hl.1.le hl.2.le hp
    have hlM : 0 ≤ l * K * D * r := by have := K.2; have := hl.1.le; positivity
    rw [← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_mul hlM, ← ENNReal.ofReal_add hc0
      (mul_nonneg hlM hT0)] at h3
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans (h2.trans h3))
    rw [hM]; nlinarith
  -- pass to the limit `l → 0⁺`
  have hcont := hVh.1.1
  have hV0 : Vh (φ 0) = 0 := hVh.1.2.1 _ h0
  have hlim : ∀ y ∈ X, Tendsto (fun l : ℝ => Vh ((1 - l) • y + l • z)) (𝓝[>] 0) (𝓝 (Vh y)) := by
    intro y hy
    have hg : Tendsto (fun l : ℝ => (1 - l) • y + l • z) (𝓝[>] 0) (𝓝[X] y) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Continuous (fun l : ℝ => (1 - l) • y + l • z) := by fun_prop
        have h := this.tendsto 0
        simp only [sub_zero, one_smul, zero_smul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with l hl
        exact hconv hy hzX (by linarith [hl.2]) hl.1.le (by ring)
    exact (hcont y hy).tendsto.comp hg
  have hF : Tendsto (fun l : ℝ => Vh ((1 - l) • x + l • z) - Vh ((1 - l) • φ 0 + l • z) - l * M)
      (𝓝[>] 0) (𝓝 (Vh x - Vh (φ 0) - 0 * M)) := by
    refine ((hlim x hx).sub (hlim _ hφ0X)).sub ?_
    exact ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  have := le_of_tendsto (b := c) hF (by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with l hl
    have := key l hl
    linarith)
  rw [hV0] at this
  linarith
