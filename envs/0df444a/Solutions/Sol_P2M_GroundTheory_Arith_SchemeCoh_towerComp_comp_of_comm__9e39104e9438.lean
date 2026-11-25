-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_towerComp_comp_of_comm__9e39104e9438
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:12.998799+00:00
-- url     : https://prove2.me/submissions/6b39b635-b027-4867-bbc8-425e86563354

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_towerComp_comp_of_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {A : Type u} [CommRing A]
  {P E Q : ℕ → Type u} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
  (τP : ∀ n, P (n + 1) →ₗ[A] P n) (τE : ∀ n, E (n + 1) →ₗ[A] E n) (τQ : ∀ n, Q (n + 1) →ₗ[A] Q n)
  (ι : ∀ n, P n →ₗ[A] E n) (π : ∀ n, E n →ₗ[A] Q n)
  (hι : ∀ n, (τE n).comp (ι (n + 1)) = (ι n).comp (τP n))
  (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
include hπ
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (n k : ℕ) :
    (towerComp τQ n k).comp (π (n + k)) = (π n).comp (towerComp τE n k) :=
  towerComp_comp_of_comm τE τQ π hπ n k
end GroundTheory.Arith.SchemeCoh
