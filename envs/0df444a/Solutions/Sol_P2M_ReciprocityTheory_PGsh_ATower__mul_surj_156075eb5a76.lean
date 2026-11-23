-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_ATower__mul_surj_156075eb5a76
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:52.352801+00:00
-- url     : https://prove2.me/submissions/a06275a6-b614-47ea-a88c-7a4dfdb25015

import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.ATower
variable {p : ℕ} (Tw : ATower R₀ p)
namespace ReciprocityTheory.PGsh.ATower
theorem _root_.solution (n : ℕ) : Function.Surjective (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) := by
  rintro ⟨k, hk⟩
  have hk' : k ∈ Ideal.span {Tw.ξ n} := by
    rw [← Tw.ker_eq n]
    simpa using hk
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hk'
  refine ⟨a, Subtype.ext ?_⟩
  show Tw.ξ n * a = k
  rw [← ha, mul_comm]
end ReciprocityTheory.PGsh.ATower
