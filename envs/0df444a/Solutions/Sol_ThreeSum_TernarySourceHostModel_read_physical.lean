-- Prove2me | solution 1 for ThreeSum.TernarySourceHostModel.read_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:51:10.033875+00:00
-- url     : https://prove2.me/submissions/868be1ae-34e1-476e-adac-5be732dd41cc

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Theorems.Thm_ThreeSum_TernarySourceHostModel_physical_eq_total

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators
variable {N : ℕ}
namespace ThreeSum.TernarySourceHostModel
theorem _root_.solution (M NL NR bank groups valueBase factor : ℕ)
    (input dictionary : ℕ → ℤ) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (ν : ℕ → ℤ)
    (ps : List (ℕ × ℕ)) (hn : ps.Nodup)
    (hmem : ∀ i j, (i,j)∈ps ↔ i<NL ∧ j<NR ∧ (M : ℤ)∣input i-dictionary j)
    (hkey : ∀ j<NR, key j<bank)
    (hinj : ∀ i j, i<bank → j<bank → enumeration i=enumeration j → i=j)
    (hread : ∀ r<groups*bank, ν (valueBase+r)=(factor : ℤ)*
      LightTernaryWeightedHistogram.total
        (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
        (fun i => weight (ps.getD i (0,0)).1) r ps.length) :
    ∀ g<groups, ∀ r<bank, ν (valueBase+g*bank+r)=(factor : ℤ)*
      physical (records M NL NR input dictionary) enumeration key group weight g (enumeration r) := by
  intro g hg r hr
  have hm := Nat.mul_le_mul_right bank (show g+1≤groups by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  rw [Nat.add_assoc,hread _ (by omega),
    physical_eq_total M NL NR bank input dictionary enumeration key group weight ps hn hmem hkey hinj g r hr]
end ThreeSum.TernarySourceHostModel
