-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_pi_c243c288e059
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:17.585884+00:00
-- url     : https://prove2.me/submissions/ec4100b9-973f-41bc-864a-596581ab54ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthCutGlobal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthCutGlobal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_add_bf6edbac3a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_add_583a49333333
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_lengths_of_subsingleton_23d6f7c0e257
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_smul_injective_pi_30b5f54dca6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_quotSMulTop_quot_f05d6b843aef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthCutGlobal_length_localized_quot_233b154d609a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped Pointwise
universe u v
open GroundTheory.Heights₂.Heights.LengthCutGlobal
variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.LengthCutGlobal
theorem _root_.solution {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) (n : ℕ) :
    Module.length C (QuotSMulTop y (Fin n → C ⧸ P)) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (Fin n → C ⧸ P)) = n := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero]
    exact lengths_of_subsingleton P y (Fin 0 → C ⧸ P)
  | succ n ih =>
    let f : (C ⧸ P) →ₗ[C] (Fin (n + 1) → C ⧸ P) := LinearMap.single C (fun _ => C ⧸ P) 0
    let g : (Fin (n + 1) → C ⧸ P) →ₗ[C] (Fin n → C ⧸ P) := LinearMap.funLeft C (C ⧸ P) Fin.succ
    have hf : Function.Injective f := fun a b h => by simpa [f] using congrFun h 0
    have hg : Function.Surjective g :=
      LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
    have H : Function.Exact f g := by
      intro v
      constructor
      · intro hv
        refine ⟨v 0, funext fun i => ?_⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [f]
        · have hj : v j.succ = 0 := congrFun hv j
          simp [f, hj, Fin.succ_ne_zero]
      · rintro ⟨t, rfl⟩
        funext j
        simp [f, g, LinearMap.funLeft, Fin.succ_ne_zero]
    rw [length_quotSMulTop_add y f g hf hg H (smul_injective_pi P hy n),
      length_localized_add P f g hf hg H, ih.1, ih.2, length_quotSMulTop_quot P hmax,
      length_localized_quot P]
    constructor <;> push_cast <;> ring
end GroundTheory.Heights₂.Heights.LengthCutGlobal
