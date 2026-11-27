-- Prove2me | solution 1 for PIW.ClassFinD.idele_class_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:08.948384+00:00
-- url     : https://prove2.me/submissions/0191d66c-2867-40c1-9cfd-8c1d3e7dd4a3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_LatticeIdealNonzero
import Theorems.Thm_PIW_ClassFinD_Icf_val_eq_of_cls
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_exists_den
import Theorems.Thm_PIW_ClassFinD_Icf_v_algF
import Theorems.Thm_PIW_ClassFinD_Icf_v_algR
import Theorems.Thm_PIW_ClassFinD_Icf_v_inv
import Theorems.Thm_PIW_ClassFinD_Icf_v_mul
import Theorems.Thm_PIW_ClassFinD_Icf_v_unit_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Icf
namespace PIW.ClassFinD
theorem _root_.solution : IdeleClassFin := by
  intro F _ _
  classical
  let rep : ClassGroup (𝓞 F) → (FiniteAdeleRing (𝓞 F) F)ˣ := fun κ =>
    if h : ∃ b : (FiniteAdeleRing (𝓞 F) F)ˣ, IsIntU b ∧ cls b = κ then h.choose else 1
  refine ⟨Finset.univ.image rep, fun a => ?_⟩
  obtain ⟨r, hr, hra⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_den (a : FiniteAdeleRing (𝓞 F) F)
  have hrF : algebraMap (𝓞 F) F r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hr
  let ur : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) (Units.mk0 _ hrF)
  let b := ur * a
  have hbw : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) =
      w.intValuation r * Valued.v ((a : FiniteAdeleRing (𝓞 F) F) w) := by
    intro w
    rw [Units.val_mul, v_mul]
    congr 1
    exact v_algR r w
  have hb : IsIntU b := by
    intro w
    have h1 : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r * (a : FiniteAdeleRing (𝓞 F) F)) w) ≤ 1 :=
      hra w
    rw [v_mul, v_algR] at h1
    rw [hbw w]
    exact h1
  have hex : ∃ b' : (FiniteAdeleRing (𝓞 F) F)ˣ, IsIntU b' ∧ cls b' = cls b := ⟨b, hb, rfl⟩
  have hb0 : IsIntU (rep (cls b)) ∧ cls (rep (cls b)) = cls b := by
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  obtain ⟨x, y, hx, hy, hv⟩ := val_eq_of_cls b (rep (cls b)) hb hb0.1 hb0.2.symm
  have hxF : algebraMap (𝓞 F) F x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hx
  have hyF : algebraMap (𝓞 F) F y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hy
  let f : Fˣ := Units.mk0 (algebraMap (𝓞 F) F y / (algebraMap (𝓞 F) F x * algebraMap (𝓞 F) F r))
    (div_ne_zero hyF (mul_ne_zero hxF hrF))
  let uf : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) f
  let e : (FiniteAdeleRing (𝓞 F) F)ˣ := (uf * rep (cls b))⁻¹ * a
  have hE : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((e : FiniteAdeleRing (𝓞 F) F) w) = 1 := by
    intro w
    have hX : w.intValuation x ≠ 0 := by
      rw [← valuation_of_algebraMap (K := F)]; exact (Valuation.ne_zero_iff _).2 hxF
    have hY : w.intValuation y ≠ 0 := by
      rw [← valuation_of_algebraMap (K := F)]; exact (Valuation.ne_zero_iff _).2 hyF
    have hR : w.intValuation r ≠ 0 := by
      rw [← valuation_of_algebraMap (K := F)]; exact (Valuation.ne_zero_iff _).2 hrF
    have hUF : Valued.v ((uf : FiniteAdeleRing (𝓞 F) F) w) =
        w.intValuation y / (w.intValuation x * w.intValuation r) := by
      have : Valued.v ((uf : FiniteAdeleRing (𝓞 F) F) w) =
          w.valuation F (algebraMap (𝓞 F) F y / (algebraMap (𝓞 F) F x * algebraMap (𝓞 F) F r)) :=
        v_algF _ w
      rw [this, map_div₀, map_mul, valuation_of_algebraMap, valuation_of_algebraMap, valuation_of_algebraMap]
    have hV : Valued.v ((uf : FiniteAdeleRing (𝓞 F) F) w) *
        Valued.v (((rep (cls b)) : FiniteAdeleRing (𝓞 F) F) w) = Valued.v ((a : FiniteAdeleRing (𝓞 F) F) w) := by
      rw [hUF, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hX hR), ← hv w, hbw w]
      ac_rfl
    have hV0 : Valued.v ((uf : FiniteAdeleRing (𝓞 F) F) w) ≠ 0 := v_unit_ne uf w
    have hB0 : Valued.v (((rep (cls b)) : FiniteAdeleRing (𝓞 F) F) w) ≠ 0 := v_unit_ne _ w
    rw [Units.val_mul, v_mul, v_inv, Units.val_mul, v_mul, hV, inv_mul_cancel₀ (v_unit_ne a w)]
  refine ⟨f, rep (cls b), Finset.mem_image.2 ⟨cls b, Finset.mem_univ _, rfl⟩, e, ?_, ?_, ?_⟩
  · intro w
    exact (hE w).le
  · intro w
    have : Valued.v (((e⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w) = 1 := by
      rw [v_inv, hE w, inv_one]
    exact this.le
  · exact (mul_inv_cancel_left (uf * rep (cls b)) a).symm
end PIW.ClassFinD
