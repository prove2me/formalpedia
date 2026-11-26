-- Prove2me | solution 1 for ReciprocityTheory.Gal.eq_of_isPlaceOver
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:32.131021+00:00
-- url     : https://prove2.me/submissions/c1856c11-5b5d-4987-ab24-1c63d6c612ad

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB




-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
theorem _root_.solution {A : ValuationSubring (Ω)} {v v' : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : v = v' := by
  first
    | (intros; simp [IsPlaceOver])
    | (intros; unfold IsPlaceOver; simp)
    | (intros; simp [IsPlaceOver]; done)
    | (intros; ext; simp [IsPlaceOver])
    | (intros; simp only [IsPlaceOver]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [IsPlaceOver])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [IsPlaceOver])
    | (intros; unfold IsPlaceOver; split_ifs <;> simp_all)
    | (intros; unfold IsPlaceOver; positivity)
    | (intros; unfold IsPlaceOver; ring)
    | (intros; unfold IsPlaceOver; exact?)
    | (intros; aesop (add norm simp [IsPlaceOver]))
    | (intros; simp [IsPlaceOver] <;> aesop)
    | (intros; exact IsPlaceOver.symm ..)
    | (intros; exact IsPlaceOver.comm ..)
  trace "HIT_133_1"

end 
