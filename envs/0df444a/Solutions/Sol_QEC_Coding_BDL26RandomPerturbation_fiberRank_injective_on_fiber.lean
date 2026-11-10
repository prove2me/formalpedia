-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.fiberRank_injective_on_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:50:58.873063+00:00
-- url     : https://prove2.me/submissions/296e9397-0aea-4e9b-ae8e-34231e5c1103

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fiberRank_strictMono
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
variable {T A : Type*} [Fintype T] [DecidableEq T] [DecidableEq A]
variable (key : T → ℕ) (f : T → A)
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (hkey : Function.Injective key)
    (a b : T) (hf : f a = f b) (hr : fiberRank key f a = fiberRank key f b) : a = b := by
  rcases lt_trichotomy (key a) (key b) with hab | hab | hab
  · have h := fiberRank_strictMono key f a b hf hab
    omega
  · exact hkey hab
  · have h := fiberRank_strictMono key f b a hf.symm hab
    omega
end QEC.Coding.BDL26RandomPerturbation
