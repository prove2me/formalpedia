-- Prove2me | solution 1 for QEC.Coding.FiniteSymplectic.form_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:42:03.065407+00:00
-- url     : https://prove2.me/submissions/3c3f599b-e41e-403b-b174-ffeda494d9b5

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u v
open QEC.Coding.FiniteSymplectic
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteSymplectic
theorem _root_.solution (a b : SymplecticVector F ι) :
    form a b = symplecticForm a b := rfl
end QEC.Coding.FiniteSymplectic
