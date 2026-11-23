-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_tens_mul_c3492ccc8731
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:37.523832+00:00
-- url     : https://prove2.me/submissions/3d3e847c-b41e-41a5-9ac5-5f8547acee5d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_tens_coeff_b71da958868c
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_coeff_mul_fintype_c8fecdf46da7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (x y : ∀ i, MonoidAlgebra k (G i)) : tens x * tens y = tens fun i => x i * y i := by
  classical
  have : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [coeff_mul_fintype, tens_coeff]
  simp only [tens_coeff, coeff_mul_fintype, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl
end Formalism.BasicNotions.Examples₂.NZ
