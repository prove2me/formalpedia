-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P25.phaseWeyl_relations_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:58:52.045061+00:00
-- url     : https://prove2.me/submissions/d6edf007-69d4-4499-b283-b1c7849dc837

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P25
noncomputable section
open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
namespace QAlgorithms.Papers.Independent.Renew46.P25

namespace S173O

variable {n : ℕ}

lemma pf_mul (a b : ℝ) : phaseFactor a * phaseFactor b = phaseFactor (a + b) := by
  unfold phaseFactor; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma pf_norm (a : ℝ) : ‖phaseFactor a‖ = 1 := by
  unfold phaseFactor
  rw [Complex.norm_exp]; simp

lemma pf_zero : phaseFactor 0 = 1 := by simp [phaseFactor]

lemma sp_sub_left (z w a : PhaseSpaceGrouped n) :
    groupedSymplecticPairing (z - w) a = groupedSymplecticPairing z a - groupedSymplecticPairing w a := by
  unfold groupedSymplecticPairing
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.sub_apply]; ring

lemma sp_add_right (z a b : PhaseSpaceGrouped n) :
    groupedSymplecticPairing z (a + b) = groupedSymplecticPairing z a + groupedSymplecticPairing z b := by
  unfold groupedSymplecticPairing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.add_apply]; ring

lemma sp_anti (z w : PhaseSpaceGrouped n) :
    groupedSymplecticPairing z w = -groupedSymplecticPairing w z := by
  unfold groupedSymplecticPairing
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma sp_zero_right (z : PhaseSpaceGrouped n) : groupedSymplecticPairing z 0 = 0 := by
  simp [groupedSymplecticPairing]

lemma sp_self (z : PhaseSpaceGrouped n) : groupedSymplecticPairing z z = 0 := by
  have := sp_anti z z; linarith

lemma sp_neg_left (z w : PhaseSpaceGrouped n) :
    groupedSymplecticPairing (-z) w = -groupedSymplecticPairing z w := by
  have := sp_sub_left 0 z w
  simp only [zero_sub] at this
  rw [this]
  have h0 : groupedSymplecticPairing (0 : PhaseSpaceGrouped n) w = 0 := by
    rw [sp_anti, sp_zero_right, neg_zero]
  rw [h0, zero_sub]

lemma clause1 (z0 z1 : PhaseSpaceGrouped n) (F : PhaseSpaceGrouped n → ℂ) :
    phaseTranslation z1 (phaseTranslation z0 F) =
      fun z => phaseFactor (-groupedSymplecticPairing z0 z1) *
        phaseTranslation z0 (phaseTranslation z1 F) z := by
  funext z
  simp only [phaseTranslation]
  rw [show z - z1 - z0 = z - z0 - z1 by abel]
  simp only [← mul_assoc, pf_mul]
  congr 2
  rw [sp_sub_left, sp_sub_left, sp_anti z1 z0]
  ring

lemma clause2 (z0 z1 : PhaseSpaceGrouped n) (F : PhaseSpaceGrouped n → ℂ) :
    phaseTranslation z0 (phaseTranslation z1 F) =
      fun z => phaseFactor (groupedSymplecticPairing z0 z1 / 2) *
        phaseTranslation (z0 + z1) F z := by
  funext z
  simp only [phaseTranslation]
  rw [show z - z0 - z1 = z - (z0 + z1) by abel]
  simp only [← mul_assoc, pf_mul]
  congr 2
  rw [sp_sub_left, sp_add_right]
  ring

lemma heis_mul (g h : PhaseSpaceGrouped n × ℝ) (F : PhaseSpaceGrouped n → ℂ) :
    phaseHeisenberg g (phaseHeisenberg h F) = phaseHeisenberg (heisenbergProduct g h) F := by
  funext z
  simp only [phaseHeisenberg, heisenbergProduct, phaseTranslation]
  rw [show z - g.1 - h.1 = z - (g.1 + h.1) by abel]
  simp only [← mul_assoc]
  rw [mul_comm (phaseFactor g.2 * phaseFactor _) (phaseFactor h.2)]
  simp only [← mul_assoc, pf_mul]
  congr 2
  rw [sp_sub_left, sp_add_right]
  ring

lemma heis_zero (F : PhaseSpaceGrouped n → ℂ) : phaseHeisenberg (0, 0) F = F := by
  funext z
  simp [phaseHeisenberg, phaseTranslation, sp_zero_right, pf_zero]

lemma cont_sp (a : PhaseSpaceGrouped n) : Continuous fun z : PhaseSpaceGrouped n => groupedSymplecticPairing z a := by
  unfold groupedSymplecticPairing
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((PiLp.continuous_apply 2 _ _).mul continuous_const).sub (continuous_const.mul (PiLp.continuous_apply 2 _ _))

lemma cont_u (g : PhaseSpaceGrouped n × ℝ) :
    Continuous fun z : PhaseSpaceGrouped n => phaseFactor g.2 * phaseFactor (-groupedSymplecticPairing z g.1 / 2) := by
  unfold phaseFactor
  refine continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul ?_))
  exact Complex.continuous_ofReal.comp (((cont_sp g.1).neg).div_const 2)

lemma heis_eq (g : PhaseSpaceGrouped n × ℝ) (F : PhaseSpaceGrouped n → ℂ) :
    phaseHeisenberg g F = fun z => (phaseFactor g.2 * phaseFactor (-groupedSymplecticPairing z g.1 / 2)) *
      (F ∘ fun z => z - g.1) z := by
  funext z; simp only [phaseHeisenberg, phaseTranslation, Function.comp_apply]; ring

lemma mp_sub (a : PhaseSpaceGrouped n) :
    MeasurePreserving (fun z : PhaseSpaceGrouped n => z - a) volume volume :=
  measurePreserving_sub_right volume a

lemma heis_memLp (g : PhaseSpaceGrouped n × ℝ) (f : PhaseGroupedL2 n) :
    MemLp (phaseHeisenberg g f) 2 volume := by
  have hf : MemLp ((f : PhaseSpaceGrouped n → ℂ) ∘ fun z => z - g.1) 2 volume :=
    (Lp.memLp f).comp_measurePreserving (mp_sub g.1)
  rw [heis_eq]
  refine hf.of_le ((cont_u g).aestronglyMeasurable.mul hf.1) (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_mul, norm_mul, pf_norm, pf_norm]; simp

lemma heis_congr (g : PhaseSpaceGrouped n × ℝ) {F F' : PhaseSpaceGrouped n → ℂ} (h : F =ᵐ[volume] F') :
    phaseHeisenberg g F =ᵐ[volume] phaseHeisenberg g F' := by
  rw [heis_eq, heis_eq]
  have := (mp_sub g.1).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [this] with z hz
  simp only [Function.comp_apply] at hz ⊢
  rw [hz]

def Φ (g : PhaseSpaceGrouped n × ℝ) (f : PhaseGroupedL2 n) : PhaseGroupedL2 n :=
  (heis_memLp g f).toLp _

lemma Φ_coe (g : PhaseSpaceGrouped n × ℝ) (f : PhaseGroupedL2 n) :
    (Φ g f : PhaseSpaceGrouped n → ℂ) =ᵐ[volume] phaseHeisenberg g f :=
  MemLp.coeFn_toLp _

lemma Φ_comp (g h : PhaseSpaceGrouped n × ℝ) (f : PhaseGroupedL2 n) :
    Φ g (Φ h f) = Φ (heisenbergProduct g h) f := by
  apply Lp.ext
  filter_upwards [Φ_coe g (Φ h f), heis_congr g (Φ_coe h f), Φ_coe (heisenbergProduct g h) f] with z h1 h2 h3
  rw [h1, h2, h3, heis_mul]

lemma Φ_zero (f : PhaseGroupedL2 n) : Φ (0, 0) f = f := by
  apply Lp.ext
  filter_upwards [Φ_coe (0, 0) f] with z h1
  rw [h1, heis_zero]

lemma Φ_add (g : PhaseSpaceGrouped n × ℝ) (f1 f2 : PhaseGroupedL2 n) :
    Φ g (f1 + f2) = Φ g f1 + Φ g f2 := by
  apply Lp.ext
  filter_upwards [Φ_coe g (f1 + f2), heis_congr g (Lp.coeFn_add f1 f2), Lp.coeFn_add (Φ g f1) (Φ g f2),
    Φ_coe g f1, Φ_coe g f2] with z h1 h2 h3 h4 h5
  rw [h1, h2, h3, Pi.add_apply, h4, h5]
  simp only [phaseHeisenberg, phaseTranslation, Pi.add_apply]
  ring

lemma Φ_smul (g : PhaseSpaceGrouped n × ℝ) (c : ℂ) (f : PhaseGroupedL2 n) :
    Φ g (c • f) = c • Φ g f := by
  apply Lp.ext
  filter_upwards [Φ_coe g (c • f), heis_congr g (Lp.coeFn_smul c f), Lp.coeFn_smul c (Φ g f),
    Φ_coe g f] with z h1 h2 h3 h4
  rw [h1, h2, h3, Pi.smul_apply, h4]
  simp only [phaseHeisenberg, phaseTranslation, Pi.smul_apply, smul_eq_mul]
  ring

lemma Φ_norm (g : PhaseSpaceGrouped n × ℝ) (f : PhaseGroupedL2 n) : ‖Φ g f‖ = ‖f‖ := by
  unfold Φ
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  rw [heis_eq]
  have e1 : eLpNorm (fun z => (phaseFactor g.2 * phaseFactor (-groupedSymplecticPairing z g.1 / 2)) *
      ((f : PhaseSpaceGrouped n → ℂ) ∘ fun z => z - g.1) z) 2 volume =
      eLpNorm ((f : PhaseSpaceGrouped n → ℂ) ∘ fun z => z - g.1) 2 volume := by
    apply eLpNorm_congr_norm_ae
    refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul, norm_mul, pf_norm, pf_norm]; simp
  rw [e1, eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) (mp_sub g.1)]

def inv (g : PhaseSpaceGrouped n × ℝ) : PhaseSpaceGrouped n × ℝ := (-g.1, -g.2)

lemma prod_inv_left (g : PhaseSpaceGrouped n × ℝ) : heisenbergProduct (inv g) g = (0, 0) := by
  simp only [heisenbergProduct, inv, neg_add_cancel, sp_neg_left, sp_self, neg_zero, zero_div, add_zero]

lemma prod_inv_right (g : PhaseSpaceGrouped n × ℝ) : heisenbergProduct g (inv g) = (0, 0) := by
  simp only [heisenbergProduct, inv, add_neg_cancel]
  rw [sp_anti, sp_neg_left, sp_self]; simp

def rho (g : PhaseSpaceGrouped n × ℝ) : PhaseGroupedL2 n ≃ₗᵢ[ℂ] PhaseGroupedL2 n where
  toFun := Φ g
  invFun := Φ (inv g)
  map_add' := Φ_add g
  map_smul' := Φ_smul g
  left_inv f := by rw [Φ_comp, prod_inv_left, Φ_zero]
  right_inv f := by rw [Φ_comp, prod_inv_right, Φ_zero]
  norm_map' := Φ_norm g

end S173O

open S173O in
theorem S173O_main (n : ℕ) (hn : 0 < n) :
    (∀ (z0 z1 : PhaseSpaceGrouped n) (F : PhaseSpaceGrouped n → ℂ),
      phaseTranslation z1 (phaseTranslation z0 F) =
        fun z => phaseFactor (-groupedSymplecticPairing z0 z1) *
          phaseTranslation z0 (phaseTranslation z1 F) z) ∧
    (∀ (z0 z1 : PhaseSpaceGrouped n) (F : PhaseSpaceGrouped n → ℂ),
      phaseTranslation z0 (phaseTranslation z1 F) =
        fun z => phaseFactor (groupedSymplecticPairing z0 z1 / 2) *
          phaseTranslation (z0 + z1) F z) ∧
    ∃ rho : (PhaseSpaceGrouped n × ℝ) → (PhaseGroupedL2 n ≃ₗᵢ[ℂ] PhaseGroupedL2 n),
      (∀ g f, (fun z => rho g f z) =ᵐ[volume] phaseHeisenberg g f) ∧
      rho (0, 0) = LinearIsometryEquiv.refl ℂ (PhaseGroupedL2 n) ∧
      (∀ g h f, rho g (rho h f) = rho (heisenbergProduct g h) f) := by
  refine ⟨clause1, clause2, S173O.rho, fun g f => Φ_coe g f, ?_, fun g h f => Φ_comp g h f⟩
  apply LinearIsometryEquiv.ext
  intro f
  exact Φ_zero f

end QAlgorithms.Papers.Independent.Renew46.P25

open QAlgorithms.Papers.Independent.Renew46.P25 in
theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ (z0 z1 : PhaseSpaceGrouped n) (F : PhaseSpaceGrouped n → ℂ),
      phaseTranslation z1 (phaseTranslation z0 F) =
        fun z => phaseFactor (-groupedSymplecticPairing z0 z1) *
          phaseTranslation z0 (phaseTranslation z1 F) z) ∧
    (∀ (z0 z1 : PhaseSpaceGrouped n) (F : PhaseSpaceGrouped n → ℂ),
      phaseTranslation z0 (phaseTranslation z1 F) =
        fun z => phaseFactor (groupedSymplecticPairing z0 z1 / 2) *
          phaseTranslation (z0 + z1) F z) ∧
    ∃ rho : (PhaseSpaceGrouped n × ℝ) → (PhaseGroupedL2 n ≃ₗᵢ[ℂ] PhaseGroupedL2 n),
      (∀ g f, (fun z => rho g f z) =ᵐ[MeasureTheory.volume] phaseHeisenberg g f) ∧
      rho (0, 0) = LinearIsometryEquiv.refl ℂ (PhaseGroupedL2 n) ∧
      (∀ g h f, rho g (rho h f) = rho (heisenbergProduct g h) f) := S173O_main n hn
