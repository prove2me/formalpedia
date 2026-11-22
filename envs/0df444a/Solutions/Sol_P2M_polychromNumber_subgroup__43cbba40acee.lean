-- Prove2me | solution 1 for P2M_polychromNumber_subgroup__43cbba40acee
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:44.427715+00:00
-- url     : https://prove2.me/submissions/6f4d3550-04ab-495a-a262-54b3355cd28f

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_subgroup
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution (H : AddSubgroup G) {S : Finset G} (hSG : (S : Set G) ⊆ H) :
    polychromNumber (G := H) (S.preimage H.subtype (by simp)) = polychromNumber S := by
  classical
  rw [polychromNumber_subgroup H, Finset.image_preimage_of_bij]
  simpa +contextual [Set.BijOn, Set.SurjOn, Set.MapsTo, Set.subset_def] using hSG
