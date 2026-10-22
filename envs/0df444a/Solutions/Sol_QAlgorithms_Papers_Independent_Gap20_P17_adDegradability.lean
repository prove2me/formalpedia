-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P17.adDegradability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:12:35.361979+00:00
-- url     : https://prove2.me/submissions/4dd896f1-09ec-4ab6-a2f6-3970e8b65312

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms

lemma g73g_ad_apply (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    adChannel eta X = !![X 0 0 + (Real.sqrt (1-eta) : ℂ) * (Real.sqrt (1-eta) : ℂ) * X 1 1,
      (Real.sqrt eta : ℂ) * X 0 1; (Real.sqrt eta : ℂ) * X 1 0,
      (Real.sqrt eta : ℂ) * (Real.sqrt eta : ℂ) * X 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [adChannel, krausApply, adKraus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sum_apply,
    Matrix.conjTranspose_apply] <;> ring

lemma g73g_recv (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    receiverChannel (adDilation eta) X = adChannel eta X := by
  rw [g73g_ad_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [receiverChannel, traceRight, adDilation, adKraus, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply] <;> ring

lemma g73g_comp (eta : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    complementaryChannel (adDilation eta) X = !![X 0 0 + (Real.sqrt eta : ℂ) * (Real.sqrt eta : ℂ) * X 1 1,
      (Real.sqrt (1-eta) : ℂ) * X 0 1; (Real.sqrt (1-eta) : ℂ) * X 1 0,
      (Real.sqrt (1-eta) : ℂ) * (Real.sqrt (1-eta) : ℂ) * X 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [complementaryChannel, traceLeft, adDilation, adKraus, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply] <;> ring

lemma g73g_sqC (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

lemma g73g_kraus (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : IsKrausFamily (adKraus eta) := by
  have a := g73g_sqC eta h0
  have b := g73g_sqC (1-eta) (by linarith)
  push_cast at b
  unfold IsKrausFamily
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [adKraus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply]
  linear_combination a + b

lemma g73g_iso (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : IsIsometry (adDilation eta) := by
  have a := g73g_sqC eta h0
  have b := g73g_sqC (1-eta) (by linarith)
  push_cast at b
  unfold IsIsometry
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [adDilation, adKraus, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, Matrix.one_apply]
  linear_combination a + b

lemma g73g_isChan (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : IsChannel (adChannel eta) :=
  ⟨2, adKraus eta, g73g_kraus eta h0 h1, fun _ => rfl⟩

theorem g73g_degr (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (1/2 ≤ eta → IsDegradable (adDilation eta)) ∧
    (eta ≤ 1/2 → IsAntidegradable (adDilation eta)) := by
  obtain ⟨h0, h1⟩ := heta
  have a := g73g_sqC eta h0
  have b := g73g_sqC (1-eta) (by linarith)
  push_cast at a b
  constructor
  · intro h
    have hpos : 0 < eta := by linarith
    set q := (1-eta)/eta with hq
    have q0 : 0 ≤ q := div_nonneg (by linarith) hpos.le
    have q1 : q ≤ 1 := by rw [hq, div_le_one hpos]; linarith
    have c := g73g_sqC q q0
    have d := g73g_sqC (1-q) (by linarith)
    have e : (Real.sqrt q : ℂ) * (Real.sqrt eta : ℂ) = (Real.sqrt (1-eta) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul q0, hq, div_mul_cancel₀ _ hpos.ne']
    have f : (q : ℂ) * eta = 1 - eta := by
      rw [hq]; push_cast; field_simp [show (eta:ℂ) ≠ 0 by exact_mod_cast hpos.ne']
    push_cast at d
    refine ⟨g73g_iso eta h0 h1, adChannel q, g73g_isChan q q0 q1, fun X => ?_⟩
    rw [g73g_recv, g73g_comp, g73g_ad_apply, g73g_ad_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [a, b, d]; linear_combination (X 1 1) * f
    · rw [← e]; ring
    · rw [← e]; ring
    · rw [a, c, b]; linear_combination (-(X 1 1)) * f
  · intro h
    have hpos : 0 < 1 - eta := by linarith
    set q := eta/(1-eta) with hq
    have q0 : 0 ≤ q := div_nonneg h0 hpos.le
    have q1 : q ≤ 1 := by rw [hq, div_le_one hpos]; linarith
    have c := g73g_sqC q q0
    have d := g73g_sqC (1-q) (by linarith)
    have e : (Real.sqrt q : ℂ) * (Real.sqrt (1-eta) : ℂ) = (Real.sqrt eta : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul q0, hq, div_mul_cancel₀ _ hpos.ne']
    have f : (q : ℂ) * (1 - eta) = eta := by
      rw [hq]; push_cast; field_simp [show (1 - (eta:ℂ)) ≠ 0 by exact_mod_cast hpos.ne']
    push_cast at d
    refine ⟨g73g_iso eta h0 h1, adChannel q, g73g_isChan q q0 q1, fun X => ?_⟩
    rw [g73g_recv, g73g_comp, g73g_ad_apply, g73g_ad_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [a, b, d]; linear_combination (X 1 1) * f
    · rw [← e]; ring
    · rw [← e]; ring
    · rw [c, b, a]; linear_combination (-(X 1 1)) * f



/-- PDF p.3: physical degrading and antidegrading maps exist in the respective
survival regimes; at eta=1/2 both properties hold. -/
theorem solution (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (1/2 ≤ eta → IsDegradable (adDilation eta)) ∧
    (eta ≤ 1/2 → IsAntidegradable (adDilation eta)) := by
  exact g73g_degr eta heta


end
