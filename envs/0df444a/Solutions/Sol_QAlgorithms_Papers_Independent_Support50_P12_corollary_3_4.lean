-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.corollary_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:47:07.246738+00:00
-- url     : https://prove2.me/submissions/537c823a-196e-4634-9fbb-8c0b97c61c4d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

end QAlgorithms.Papers.Independent.Support50.P12

namespace A3S55C34
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open scoped Matrix ComplexOrder MatrixOrder

variable {I : Type} [Fintype I] [DecidableEq I]

lemma cont (X : Mat I) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum).continuousOn f

lemma isClosed_alg (A : StarSubalgebra ℂ (Mat I)) : IsClosed (A : Set (Mat I)) :=
  (Subalgebra.toSubmodule A.toSubalgebra).closed_of_finiteDimensional

lemma supp_mem (A : StarSubalgebra ℂ (Mat I)) {X : Mat I} (hX : X ∈ A) :
    supportPower X 0 ∈ A := by
  have := isClosed_alg A
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) _ hX

lemma supp_sa (X : Mat I) : IsSelfAdjoint (supportPower X 0) := by
  unfold supportPower; exact cfc_predicate _ _

lemma supp_herm (X : Mat I) : (supportPower X 0)ᴴ = supportPower X 0 := supp_sa X

lemma supp_idem (X : Mat I) :
    supportPower X 0 * supportPower X 0 = supportPower X 0 := by
  unfold supportPower
  rw [← cfc_mul _ _ X (cont X _) (cont X _)]
  congr 1; funext x; by_cases hx : x = 0 <;> simp [hx]

lemma mul_supp {X : Mat I} (hX : X.IsHermitian) : X * supportPower X 0 = X := by
  unfold supportPower
  conv_lhs => arg 1; rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  rw [← cfc_mul _ _ X (cont X _) (cont X _)]
  conv_rhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  congr 1; funext x; by_cases hx : x = 0 <;> simp [hx]

lemma supp_mul {X : Mat I} (hX : X.IsHermitian) : supportPower X 0 * X = X := by
  have := congrArg Matrix.conjTranspose (mul_supp hX)
  rwa [Matrix.conjTranspose_mul, supp_herm, hX.eq] at this

lemma supportPower_one {X : Mat I} (hX : X.IsHermitian) : supportPower X 1 = X := by
  unfold supportPower
  conv_rhs => rw [← cfc_id' ℝ X hX.isSelfAdjoint]
  congr 1; funext x; by_cases hx : x = 0 <;> simp [hx]


lemma supp_le {X : Mat I} (hX : X.PosSemidef) :
    ∃ c : ℝ, 0 ≤ c ∧ (c • X - supportPower X 0).PosSemidef := by
  refine ⟨∑ i, (hX.1.eigenvalues i)⁻¹, Finset.sum_nonneg fun i _ => inv_nonneg.2 (hX.eigenvalues_nonneg i), ?_⟩
  set c := ∑ i, (hX.1.eigenvalues i)⁻¹
  have h : c • X - supportPower X 0 =
      cfc (fun x : ℝ => c * x - (if x = 0 then 0 else Real.rpow x 0)) X := by
    rw [cfc_sub _ _ X (cont X _) (cont X _), cfc_const_mul _ _ X (cont X _),
      cfc_id' ℝ X hX.1.isSelfAdjoint]
    rfl
  rw [h, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro x hx
  obtain ⟨j, rfl⟩ := hX.1.spectrum_real_eq_range_eigenvalues ▸ hx
  have hj := hX.eigenvalues_nonneg j
  by_cases h0 : hX.1.eigenvalues j = 0
  · simp [h0]
  · have hpos : 0 < hX.1.eigenvalues j := lt_of_le_of_ne hj (Ne.symm h0)
    have : (hX.1.eigenvalues j)⁻¹ ≤ c :=
      Finset.single_le_sum (f := fun i => (hX.1.eigenvalues i)⁻¹)
        (fun i _ => inv_nonneg.2 (hX.eigenvalues_nonneg i)) (Finset.mem_univ j)
    have hr : (hX.1.eigenvalues j).rpow 0 = 1 := Real.rpow_zero _
    simp only [h0, if_false, hr]
    have : 1 ≤ c * hX.1.eigenvalues j := by
      calc (1:ℝ) = (hX.1.eigenvalues j)⁻¹ * hX.1.eigenvalues j := by field_simp
        _ ≤ c * hX.1.eigenvalues j := by gcongr
    linarith

lemma le_const {Y : Mat I} (hY : Y.PosSemidef) :
    ∃ T : ℝ, 0 ≤ T ∧ (T • (1 : Mat I) - Y).PosSemidef := by
  refine ⟨∑ i, hY.1.eigenvalues i, Finset.sum_nonneg fun i _ => hY.eigenvalues_nonneg i, ?_⟩
  set T := ∑ i, hY.1.eigenvalues i
  have h : T • (1 : Mat I) - Y = cfc (fun x : ℝ => T - x) Y := by
    rw [cfc_sub _ _ Y (cont Y _) (cont Y _), cfc_const T Y, cfc_id' ℝ Y hY.1.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
  rw [h, ← Matrix.nonneg_iff_posSemidef]
  apply cfc_nonneg
  intro x hx
  obtain ⟨j, rfl⟩ := hY.1.spectrum_real_eq_range_eigenvalues ▸ hx
  have := Finset.single_le_sum (f := fun i => hY.1.eigenvalues i)
        (fun i _ => hY.eigenvalues_nonneg i) (Finset.mem_univ j)
  exact sub_nonneg.2 this

lemma dom {X Y : Mat I} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ∃ K : ℝ, (K • X - supportPower X 0 * Y * supportPower X 0).PosSemidef := by
  obtain ⟨c, hc0, hc⟩ := supp_le hX
  obtain ⟨T, hT0, hT⟩ := le_const hY
  set s := supportPower X 0
  have h1 : (s * (T • (1 : Mat I) - Y) * sᴴ).PosSemidef := hT.mul_mul_conjTranspose_same s
  rw [supp_herm] at h1
  have h2 : (T • (c • X - s)).PosSemidef := hc.smul hT0
  refine ⟨T * c, ?_⟩
  have : (T * c) • X - s * Y * s = s * (T • (1 : Mat I) - Y) * s + T • (c • X - s) := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, supp_idem, smul_sub, smul_smul]
    abel
  rw [this]; exact h1.add h2


variable {J : Type} [Fintype J] [DecidableEq J]

/-- real trace functional of a linear map -/
noncomputable def trL (M : Mat I →ₗ[ℂ] Mat J) : Mat I →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((Matrix.traceLinearMap J ℂ ℂ ∘ₗ M).restrictScalars ℝ)

@[simp] lemma trL_apply (M : Mat I →ₗ[ℂ] Mat J) (Z : Mat I) : trL M Z = (M Z).trace.re := rfl

lemma quad_zero {a b : ℝ} (hb : 0 ≤ b) (h : ∀ t : ℝ, 0 ≤ t * a + t * t * b) : a = 0 := by
  have h1 := h (-a / (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have : -a / (b + 1) * a + -a / (b + 1) * (-a / (b + 1)) * b = -(a ^ 2) / (b + 1) ^ 2 := by
    field_simp; ring
  rw [this] at h1
  have : a ^ 2 ≤ 0 := by
    have := div_nonneg_iff.mp h1 |>.elim (fun h => h.1) (fun h => by nlinarith [h.2, sq_nonneg (b+1), pow_pos hb1 2])
    linarith
  nlinarith [sq_nonneg a]

lemma quad (A : StarSubalgebra ℂ (Mat I)) (L : Mat I →ₗ[ℝ] ℝ)
    (hpos : ∀ Z ∈ A, Z.PosSemidef → 0 ≤ L Z) {s Y : Mat I} (hsA : s ∈ A) (hsh : sᴴ = s)
    (hYA : Y ∈ A) (hYp : Y.PosSemidef) (h0 : L (s * Y * s) = 0) :
    L Y = L ((1 - s) * Y * (1 - s)) := by
  set u := 1 - s
  have huA : u ∈ A := sub_mem (one_mem _) hsA
  have huh : uᴴ = u := by simp [u, Matrix.conjTranspose_sub, hsh]
  set C := s * Y * u + u * Y * s
  set D := u * Y * u
  have hDA : D ∈ A := mul_mem (mul_mem huA hYA) huA
  have hDp : D.PosSemidef := by
    have := hYp.mul_mul_conjTranspose_same u; rwa [huh] at this
  have hY : Y = s * Y * s + C + D := by
    have : Y = (s + u) * Y * (s + u) := by simp [u]
    conv_lhs => rw [this]
    simp only [C, D, add_mul, mul_add]; abel
  have hC : L C = 0 := by
    apply quad_zero (hpos D hDA hDp)
    intro t
    have hW : ((s + t • u) * Y * (s + t • u)).PosSemidef := by
      have := hYp.mul_mul_conjTranspose_same (s + t • u)
      rwa [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsh, huh, star_trivial] at this
    have hWA : (s + t • u) * Y * (s + t • u) ∈ A := by
      refine mul_mem (mul_mem (add_mem hsA ?_) hYA) (add_mem hsA ?_) <;>
      · rw [← algebraMap_smul ℂ t u]; exact A.smul_mem huA _
    have hexp : (s + t • u) * Y * (s + t • u) = s * Y * s + t • C + (t * t) • D := by
      simp only [C, D, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
      abel
    have := hpos _ hWA hW
    rw [hexp, map_add, map_add, h0, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
    linarith
  conv_lhs => rw [hY]
  rw [map_add, map_add, h0, hC]; simp

lemma tr_proj_nonneg {W P : Mat J} (hW : W.PosSemidef) (hPh : Pᴴ = P) (hPi : P * P = P) :
    0 ≤ (W * P).trace.re := by
  have : (W * P).trace = (P * W * Pᴴ).trace := by
    rw [hPh]
    calc (W * P).trace = (W * P * P).trace := by rw [mul_assoc, hPi]
      _ = (P * (W * P)).trace := Matrix.trace_mul_comm _ _
      _ = (P * W * P).trace := by rw [mul_assoc]
  rw [this]
  exact (Complex.nonneg_iff.mp (hW.mul_mul_conjTranspose_same P).trace_nonneg).1


lemma logmono {a b : ℝ} (h : a ≤ b) :
    ((-1 : ℝ) : EReal) * QAlgorithms.Papers.Independent.Dependency50.P28.logNonnegativeExtended b ≤
    ((-1 : ℝ) : EReal) * QAlgorithms.Papers.Independent.Dependency50.P28.logNonnegativeExtended a := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P28.logNonnegativeExtended
  by_cases ha : 0 < a
  · have hb : 0 < b := lt_of_lt_of_le ha h
    rw [if_pos ha, if_pos hb, ← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have := Real.log_le_log ha h; linarith
  · rw [if_neg ha, EReal.coe_mul_bot_of_neg (by norm_num)]; exact le_top

end A3S55C34

open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr logNonnegativeExtended)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open A3S55C34
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi) (ht : AlgebraTraceNonincreasing A Phi)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef)
    (htr : tr (Phi X) = tr X) :
    tr (Y * supp X) ≤ tr (Phi Y * supp (Phi X)) ∧
    tr (Phi Y * (1 - supp (Phi X))) ≤ tr (Y * (1 - supp X)) ∧
    petzRenyi 0 (Phi X) (Phi Y) ≤ petzRenyi 0 X Y := by
  have hPX := hp X hX hXp
  have hPY := hp Y hY hYp
  simp only [supp]
  set s := supportPower X 0 with hs
  set p := supportPower (Phi X) 0 with hpdef
  have hsA : s ∈ A := supp_mem A hX
  have hsh : sᴴ = s := supp_herm X
  have hph : pᴴ = p := supp_herm (Phi X)
  have hpi : p * p = p := supp_idem (Phi X)
  have hqh : (1 - p)ᴴ = 1 - p := by simp [Matrix.conjTranspose_sub, hph]
  have hqi : (1 - p) * (1 - p) = 1 - p := by simp [sub_mul, mul_sub, hpi]
  have hsi : s * s = s := supp_idem X
  have hui : (1 - s) * (1 - s) = 1 - s := by simp [sub_mul, mul_sub, hsi]
  have huh : (1 - s)ᴴ = 1 - s := by simp [Matrix.conjTranspose_sub, hsh]
  let G : Mat I →ₗ[ℝ] ℝ := trL (LinearMap.mulRight ℂ (1 - p) ∘ₗ Phi)
  let F : Mat I →ₗ[ℝ] ℝ := trL LinearMap.id - trL (LinearMap.mulRight ℂ p ∘ₗ Phi)
  have hGapp : ∀ Z, G Z = (Phi Z * (1 - p)).trace.re := fun Z => rfl
  have hFapp : ∀ Z, F Z = Z.trace.re - (Phi Z * p).trace.re := fun Z => rfl
  have hFG : ∀ Z, F Z = (Z.trace.re - (Phi Z).trace.re) + G Z := by
    intro Z; rw [hFapp, hGapp, mul_sub, mul_one, Matrix.trace_sub, Complex.sub_re]; ring
  have hGpos : ∀ Z ∈ A, Z.PosSemidef → 0 ≤ G Z := fun Z hZ hZp =>
    tr_proj_nonneg (hp Z hZ hZp) hqh hqi
  have hFpos : ∀ Z ∈ A, Z.PosSemidef → 0 ≤ F Z := fun Z hZ hZp => by
    rw [hFG]; have := ht Z hZ hZp; have := hGpos Z hZ hZp
    unfold tr at *; linarith
  have hGX : G X = 0 := by rw [hGapp, mul_sub, mul_one, mul_supp hPX.1, sub_self]; simp
  have hFX : F X = 0 := by rw [hFG, hGX]; unfold tr at htr; linarith
  obtain ⟨K, hK⟩ := dom hXp hYp
  have hsYsA : s * Y * s ∈ A := mul_mem (mul_mem hsA hY) hsA
  have hsYsp : (s * Y * s).PosSemidef := by
    have := hYp.mul_mul_conjTranspose_same s; rwa [hsh] at this
  have hKA : K • X - s * Y * s ∈ A := by
    refine sub_mem ?_ hsYsA
    rw [← algebraMap_smul ℂ K X]; exact A.smul_mem hX _
  have zero_of : ∀ L : Mat I →ₗ[ℝ] ℝ, (∀ Z ∈ A, Z.PosSemidef → 0 ≤ L Z) → L X = 0 →
      L (s * Y * s) = 0 := by
    intro L hpos hLX
    refine le_antisymm ?_ (hpos _ hsYsA hsYsp)
    have := hpos _ hKA hK
    rw [map_sub, map_smul, hLX, smul_zero] at this
    linarith
  have hG := quad A G hGpos hsA hsh hY hYp (zero_of G hGpos hGX)
  have hF := quad A F hFpos hsA hsh hY hYp (zero_of F hFpos hFX)
  set W := (1 - s) * Y * (1 - s) with hW
  have hWA : W ∈ A := mul_mem (mul_mem (sub_mem (one_mem _) hsA) hY) (sub_mem (one_mem _) hsA)
  have hWp : W.PosSemidef := by
    have := hYp.mul_mul_conjTranspose_same (1 - s); rwa [huh] at this
  have htrW : W.trace = (Y * (1 - s)).trace := by
    rw [hW, Matrix.trace_mul_comm, ← mul_assoc, hui, Matrix.trace_mul_comm]
  have hPW := hp W hWA hWp
  have hpW : 0 ≤ (Phi W * p).trace.re := tr_proj_nonneg hPW hph hpi
  have htW := ht W hWA hWp
  unfold tr at htW
  have hGW : G W ≤ (Phi W).trace.re := by
    have := hFG W; rw [hFapp] at this; linarith
  have h2 : (Phi Y * (1 - p)).trace.re ≤ (Y * (1 - s)).trace.re := by
    rw [← hGapp, hG, ← htrW]; linarith
  have h1 : (Y * s).trace.re ≤ (Phi Y * p).trace.re := by
    have e1 := hFapp Y
    have e2 := hFapp W
    have e3 : (Y * (1 - s)).trace.re = Y.trace.re - (Y * s).trace.re := by
      rw [mul_sub, mul_one, Matrix.trace_sub, Complex.sub_re]
    rw [htrW, e3] at e2
    linarith
  refine ⟨h1, h2, ?_⟩
  unfold petzRenyi
  rw [if_pos (Or.inr (by norm_num)), if_pos (Or.inr (by norm_num))]
  norm_num only [sub_zero]
  rw [supportPower_one hPY.1, supportPower_one hYp.1, ← hs, ← hpdef]
  have := logmono (a := tr (s * Y)) (b := tr (p * Phi Y)) (by
    unfold tr; rw [Matrix.trace_mul_comm s, Matrix.trace_mul_comm p]; exact h1)
  simpa using this
