-- Prove2me | solution 1 for SizeRamsey.Plan.equality_residual_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:56.582905+00:00
-- url     : https://prove2.me/submissions/f735a830-9086-485d-bd2c-a884ee15df50

module
public import Definitions.Def_SizeRamsey_Universal
public import Definitions.Def_SizeRamsey_Tightness
public import Theorems.Thm_SizeRamsey_Plan_edgeCount_components
public import Theorems.Thm_SizeRamsey_Plan_tau4_components
public import Theorems.Thm_SizeRamsey_Plan_universal


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (D : Finset V) (c : ℕ)
    (ht : 4 * tau4 G = edgeCount G)
    (hlift : tau4 G ≤ tau4 (erase G D) + c)
    (hcount : edgeCount (erase G D) + 4 * c = edgeCount G) :
    tau4 G = tau4 (erase G D) + c ∧
    ∀ C : (erase G D).ConnectedComponent,
      4 * tau4 (compGraph (erase G D) C) =
        edgeCount (compGraph (erase G D) C) := by
  have hbound := universal (erase G D)
  have heq : tau4 G = tau4 (erase G D) + c := by omega
  have hres : 4 * tau4 (erase G D) = edgeCount (erase G D) := by omega
  refine ⟨heq, ?_⟩
  have hsum : (∑ C : (erase G D).ConnectedComponent,
      4 * tau4 (compGraph (erase G D) C)) =
      ∑ C : (erase G D).ConnectedComponent,
        edgeCount (compGraph (erase G D) C) := by
    rw [← Finset.mul_sum, ← tau4_components, ← edgeCount_components]
    exact hres
  exact fun C => (Finset.sum_eq_sum_iff_of_le
    (fun C _ => universal (compGraph (erase G D) C))).mp hsum C (Finset.mem_univ C)
end SizeRamsey.Plan
