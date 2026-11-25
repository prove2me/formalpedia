-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.length_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:28.85284+00:00
-- url     : https://prove2.me/submissions/37bd7e0e-41e4-460d-9328-4378586ecf2f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_exists_unit_ord
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_ord_sub_one_nonneg_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_length_residue
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_smul_gen
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_smul_self
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_As_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_ball_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_ne_top
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_nonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_units_add_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
variable {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [IsScalarTower O A V] {e : V}
open Classical
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Finite (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (hfin : Module.Finite O ↥(As O A))
    (he : IsGen A e) (c d : Pts O A → ℤ) (ζ₀ : Pts O A)
    (hd : ∀ ζ, d ζ = c ζ + if ζ = ζ₀ then 1 else 0) :
    Module.length O (↥(ballO ϖ e d) ⧸ (ballO ϖ e c).comap (ballO ϖ e d).subtype) = fdeg ζ₀ := by
  classical
  obtain ⟨w, hw⟩ := exists_unit_ord K h (fun ζ => -d ζ)
  have hwi : ∀ ζ, ord ϖ ζ ((w⁻¹ : Aˣ) : A) = ((d ζ : ℤ) : WithTop ℤ) := by
    intro ζ
    have e := ord_units_add_inv (ζ := ζ) h w
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (ord_ne_top (ζ := ζ) h (w⁻¹).isUnit.mem_nonZeroDivisors)
    rw [← hk, hw ζ] at e
    rw [← hk]
    have e' : -d ζ + k = 0 := by exact_mod_cast e
    congr 1
    omega
  have hov : ∀ (c' : Pts O A → ℤ) (b : ↥(As O A)) (ζ : Pts O A),
      ordV ϖ ζ e c' (((b : A) * w) • e) = ord ϖ ζ (b : A) + ((c' ζ - d ζ : ℤ) : WithTop ℤ) := by
    intro c' b ζ
    simp only [ordV]
    rw [coord_smul_gen he, ord_mul (ζ := ζ) h, hw ζ, add_assoc, ← WithTop.coe_add]
    rw [show -d ζ + c' ζ = c' ζ - d ζ by ring]
  have hmemd : ∀ b : ↥(As O A), ((b : A) * w) • e ∈ ballO ϖ e d := by
    intro b
    show ((b : A) * w) • e ∈ ball ϖ e d
    rw [mem_ball_iff (h := h) (he := he)]
    intro ζ
    rw [hov, sub_self, WithTop.coe_zero, add_zero]
    exact ord_nonneg (ζ := ζ) h b.2
  let f : ↥(As O A) →ₗ[O] ↥(ballO ϖ e d) :=
    { toFun := fun b => ⟨((b : A) * w) • e, hmemd b⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp only [Subalgebra.coe_add, add_mul, add_smul, Submodule.coe_add]
      map_smul' := fun r x => by
        apply Subtype.ext
        simp only [Subalgebra.coe_smul, RingHom.id_apply, Submodule.coe_smul, smul_mul_assoc,
          smul_assoc] }
  let G := ((ballO ϖ e c).comap (ballO ϖ e d).subtype).mkQ ∘ₗ f
  have hsurj : Function.Surjective G := by
    intro y
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
    have hv : ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e d (v : V) := (mem_ball_iff (c := d) (h := h) (he := he) (v := (v : V))).mp v.2
    have hb : (coord e (v : V) : A) * ((w⁻¹ : Aˣ) : A) ∈ As O A := by
      rw [mem_As_iff h]
      intro ζ
      rw [ord_mul (ζ := ζ) h, hwi ζ]
      exact hv ζ
    refine ⟨⟨_, hb⟩, ?_⟩
    show Submodule.mkQ _ (f ⟨_, hb⟩) = Submodule.mkQ _ v
    congr 1
    apply Subtype.ext
    show ((coord e (v : V) : A) * ((w⁻¹ : Aˣ) : A) * w) • e = v
    rw [mul_assoc, Units.inv_mul, mul_one, coord_smul_self he]
  have hker : LinearMap.ker G = ζ₀.asIdeal.restrictScalars O := by
    ext b
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
    show Submodule.mkQ _ (f b) = 0 ↔ b ∈ ζ₀.asIdeal
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply]
    show ((b : A) * w) • e ∈ ball ϖ e c ↔ b ∈ ζ₀.asIdeal
    rw [mem_ball_iff (h := h) (he := he)]
    constructor
    · intro H
      have := H ζ₀
      rw [hov, hd ζ₀, if_pos rfl, show c ζ₀ - (c ζ₀ + 1) = (-1 : ℤ) by ring] at this
      exact (ord_sub_one_nonneg_iff h ζ₀ b).mp this
    · intro hb ζ
      rw [hov, hd ζ]
      by_cases hz : ζ = ζ₀
      · subst hz
        rw [if_pos rfl, show c ζ - (c ζ + 1) = (-1 : ℤ) by ring]
        exact (ord_sub_one_nonneg_iff h ζ b).mpr hb
      · rw [if_neg hz, show c ζ - (c ζ + 0) = (0 : ℤ) by ring, WithTop.coe_zero, add_zero]
        exact ord_nonneg (ζ := ζ) h b.2
  rw [← (G.quotKerEquivOfSurjective hsurj).length_eq,
    (Submodule.quotEquivOfEq _ _ hker).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv O ζ₀.asIdeal).length_eq]
  exact length_residue hfin ζ₀
end PI.UnitaryGroupMassFormula.BallQuotLen
