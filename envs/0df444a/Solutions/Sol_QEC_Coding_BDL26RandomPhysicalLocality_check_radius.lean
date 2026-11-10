-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPhysicalLocality.check_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:48:59.020206+00:00
-- url     : https://prove2.me/submissions/dc14310e-4f03-4554-9e6c-45e15b2bb3e7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbeddingCoordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_x_checkSupport
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_mem_z_checkSupport
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.mem_x_checkSupport
attribute [local simp] QEC.Coding.BDL26CSSHamiltonian.mem_z_checkSupport



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPhysicalLocality
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26TannerLocalRegularity
open BDL26QuantitativeBounds BDL26DecodingGraph BDL26CSSHamiltonian
open Semantics Semantics.Davies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26RandomPhysicalLocality
theorem _root_.solution (S : OddScale) (n : Nat) (J : Vertex (state S n).presentation → E)
    {t : ℝ} (hJ : IsBoundedDensityLocalMap (state S n).presentation J t)
    (j : Sum (ZLabel S n) (XLabel S n)) (r : Physical S n)
    (hr : r ∈ checkSupport S n j) : dist (J (.q r)) (checkCenter S n J j) ≤ 1 := by
  cases j with
  | inl z => exact hJ.2.1 r z ((mem_z_checkSupport S n z r).mp hr)
  | inr x => exact (dist_comm _ _).trans_le (hJ.1 x r ((mem_x_checkSupport S n x r).mp hr))
end QEC.Coding.BDL26RandomPhysicalLocality
