-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P49.gaussianComposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:50:36.616758+00:00
-- url     : https://prove2.me/submissions/0a3e0736-35bd-4b8e-8b71-c5d9271ec536

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier30.P14
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace X4GC

open QAlgorithms.Papers.Independent.Claimed50.P49

/-- reindex an ℓ² vector along an equivalence -/
def reHil {I J : Type} (e : I ≃ J) (v : Hilbert J) : Hilbert I :=
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hm : Memℓp (fun i => (v : ∀ j, (fun _ : J => ℂ) j) (e i)) 2 := by
    rw [memℓp_gen_iff hp]
    exact (e.summable_iff (f := fun j => ‖v j‖ ^ (2 : ℝ≥0∞).toReal)).mpr
      ((memℓp_gen_iff hp).mp (lp.memℓp v))
  ⟨_, hm⟩

lemma reHil_norm {I J : Type} (e : I ≃ J) (v : Hilbert J) : ‖reHil e v‖ = ‖v‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 1
  exact e.tsum_eq (fun j => ‖v j‖ ^ (2 : ℝ≥0∞).toReal)

lemma density_reindex {I J : Type} (e : I ≃ J) {X : Matrix J J ℂ} (hX : IsDensity X) :
    IsDensity (fun i j => X (e i) (e j)) := by
  obtain ⟨⟨N⟩, hpos, hsum, htr⟩ := hX
  refine ⟨⟨⟨fun n => reHil e (N.left n), fun n => reHil e (N.right n), ?_, ?_⟩⟩, ?_, ?_, ?_⟩
  · simpa only [reHil_norm] using N.summable
  · intro i j; exact N.coefficients (e i) (e j)
  · intro s z
    have h := hpos (s.map e.toEmbedding) (fun j => z (e.symm j))
    simp only [Finset.sum_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at h
    exact h
  · exact (e.summable_iff (f := fun j => (X j j).re)).mpr hsum
  · rw [e.tsum_eq (fun j => (X j j).re)]; exact htr

lemma tc_comp {I J K : Type} {E1 : Matrix I I ℂ → Matrix J J ℂ} {E2 : Matrix J J ℂ → Matrix K K ℂ}
    (h1 : IsTraceClassChannel E1) (h2 : IsTraceClassChannel E2) : IsTraceClassChannel (E2 ∘ E1) := by
  obtain ⟨a1, b1, c1, d1⟩ := h1
  obtain ⟨a2, b2, c2, d2⟩ := h2
  refine ⟨fun X hX => a2 _ (a1 X hX), fun X Y hX hY => ?_, fun c X hX => ?_, fun n rho => ?_⟩
  · simp only [Function.comp_apply]; rw [b1 X Y hX hY, b2 _ _ (a1 X hX) (a1 Y hY)]
  · simp only [Function.comp_apply]; rw [c1 c X hX, c2 c _ (a1 X hX)]
  · exact d2 n ⟨tensorApply E1 rho.coefficients, d1 n rho⟩

lemma density_out {I J : Type} {E : Matrix I I ℂ → Matrix J J ℂ} (hE : IsTraceClassChannel E)
    {X : Matrix I I ℂ} (hX : IsDensity X) : IsDensity (E X) := by
  set e : I × Fin 1 ≃ I := Equiv.prodUnique I (Fin 1)
  have h1 : IsDensity (fun p q : I × Fin 1 => X (e p) (e q)) := density_reindex e hX
  have h2 := hE.2.2.2 1 ⟨_, h1⟩
  have h3 : tensorApply E (fun p q : I × Fin 1 => X (e p) (e q)) =
      fun p q : J × Fin 1 => E X p.1 q.1 := rfl
  rw [h3] at h2
  have h4 := density_reindex (Equiv.prodUnique J (Fin 1)).symm h2
  exact h4

lemma quad_add (A B : RealMatrix) (z : Fin 2 → ℝ) : quadratic (A + B) z = quadratic A z + quadratic B z := by
  simp only [quadratic, Matrix.add_apply, Fin.sum_univ_two]; ring

lemma quad_conj (A K : RealMatrix) (z : Fin 2 → ℝ) :
    quadratic (K.transpose * A * K) z = quadratic A (K.mulVec z) := by
  simp only [quadratic, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
  ring

lemma mink {A B : RealMatrix} (hA : A 1 0 = A 0 1) (hB : B 1 0 = B 0 1)
    (ha0 : 0 ≤ A 0 0) (ha1 : 0 ≤ A 1 1) (hb0 : 0 ≤ B 0 0) (hb1 : 0 ≤ B 1 1)
    (hdA : 0 ≤ A.det) (hdB : 0 ≤ B.det) :
    (Real.sqrt A.det + Real.sqrt B.det) ^ 2 ≤ (A + B).det := by
  set s := Real.sqrt A.det
  set t := Real.sqrt B.det
  have hs : s ^ 2 = A.det := Real.sq_sqrt hdA
  have ht : t ^ 2 = B.det := Real.sq_sqrt hdB
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  rw [Matrix.det_fin_two] at hs ht ⊢
  simp only [Matrix.add_apply]
  rw [hA] at hs ⊢; rw [hB] at ht ⊢
  set a := A 0 0; set b := A 0 1; set c := A 1 1
  set p := B 0 0; set q := B 0 1; set r := B 1 1
  have hX : 0 ≤ a * r + c * p := by positivity
  have hm : (2 * (s * t + b * q)) ^ 2 ≤ (a * r + c * p) ^ 2 := by
    nlinarith [sq_nonneg (a * r - c * p), sq_nonneg (s * q - b * t), mul_nonneg ha0 hb1, mul_nonneg ha1 hb0]
  have hle : 2 * (s * t + b * q) ≤ a * r + c * p := by
    by_contra hcon
    push Not at hcon
    nlinarith
  nlinarith

theorem admissible_comp {g1 g2 : GaussianData} (h1 : GaussianAdmissible g1) (h2 : GaussianAdmissible g2) :
    GaussianAdmissible (composeData g1 g2) := by
  obtain ⟨s1, p1, d1⟩ := h1
  obtain ⟨s2, p2, d2⟩ := h2
  simp only [GaussianAdmissible, composeData]
  set A := g2.K.transpose * g1.alpha * g2.K
  have hAs : A.transpose = A := by
    simp only [A, Matrix.transpose_mul, Matrix.transpose_transpose, s1, Matrix.mul_assoc]
  have hAq : ∀ z, 0 ≤ quadratic A z := fun z => by rw [quad_conj]; exact p1 _
  refine ⟨by rw [Matrix.transpose_add, hAs, s2], fun z => by rw [quad_add]; exact add_nonneg (hAq z) (p2 z), ?_⟩
  have e0 : ∀ (M : RealMatrix), quadratic M (Pi.single 0 1) = M 0 0 := fun M => by
    simp [quadratic, Fin.sum_univ_two]
  have e1 : ∀ (M : RealMatrix), quadratic M (Pi.single 1 1) = M 1 1 := fun M => by
    simp [quadratic, Fin.sum_univ_two]
  have sym : ∀ (M : RealMatrix), M.transpose = M → M 1 0 = M 0 1 := fun M h => by
    have := congrFun (congrFun h 0) 1; simpa using this
  have hdA : A.det = g2.K.det ^ 2 * g1.alpha.det := by
    simp only [A, Matrix.det_mul, Matrix.det_transpose]; ring
  have hdA0 : 0 ≤ A.det := by rw [hdA]; exact mul_nonneg (sq_nonneg _) (le_trans (sq_nonneg _) d1)
  have hdB0 : 0 ≤ g2.alpha.det := le_trans (sq_nonneg _) d2
  have hM := mink (sym A hAs) (sym _ s2) (e0 A ▸ hAq _) (e1 A ▸ hAq _) (e0 g2.alpha ▸ p2 _)
    (e1 g2.alpha ▸ p2 _) hdA0 hdB0
  refine le_trans ?_ hM
  have hsA : |g2.K.det * ((g1.K.det - 1) / 2)| ≤ Real.sqrt A.det := by
    apply Real.abs_le_sqrt; rw [hdA, mul_pow]; exact mul_le_mul_of_nonneg_left d1 (sq_nonneg _)
  have hsB : |(g2.K.det - 1) / 2| ≤ Real.sqrt g2.alpha.det := Real.abs_le_sqrt d2
  have htri : |((g1.K * g2.K).det - 1) / 2| ≤ |g2.K.det * ((g1.K.det - 1) / 2)| + |(g2.K.det - 1) / 2| := by
    rw [Matrix.det_mul]
    calc |(g1.K.det * g2.K.det - 1) / 2| = |g2.K.det * ((g1.K.det - 1) / 2) + (g2.K.det - 1) / 2| := by
          congr 1; ring
      _ ≤ _ := abs_add_le _ _
  calc (((g1.K * g2.K).det - 1) / 2) ^ 2 = |((g1.K * g2.K).det - 1) / 2| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt A.det + Real.sqrt g2.alpha.det) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (htri.trans (add_le_add hsA hsB)) 2

end X4GC

open X4GC QAlgorithms.Papers.Independent.Claimed50.P49 in
theorem solution (E1 E2 : FockMap) (g1 g2 : GaussianData)
    (h1 : IsGaussianChannel E1 g1) (h2 : IsGaussianChannel E2 g2) :
    IsGaussianChannel (E2 ∘ E1) (composeData g1 g2) := by
  obtain ⟨t1, a1, c1⟩ := h1
  obtain ⟨t2, a2, c2⟩ := h2
  refine ⟨tc_comp t1 t2, admissible_comp a1 a2, fun rho z => ?_⟩
  have hd : IsDensity (E1 rho.coefficients) := density_out t1 rho.density
  have := c2 ⟨E1 rho.coefficients, hd⟩ z
  simp only [Function.comp_apply]
  rw [this]
  simp only [gaussianTransform]
  rw [c1 rho (g2.K.mulVec z)]
  simp only [gaussianTransform, composeData, Matrix.mulVec_mulVec, mul_assoc, ← Complex.exp_add]
  congr 2
  rw [quad_add, ← Matrix.mul_assoc, quad_conj]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply, Fin.sum_univ_two]
  push_cast
  ring
