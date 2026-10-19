-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_count_from_coefficients_and_jets
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:25:49.89776+00:00
-- url     : https://prove2.me/submissions/29b0173f-734f-4dde-bfaf-ca7314479c10

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_block_exists00
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_block_exists01
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_block_exists02
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_block_exists03
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_block_exists04
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_block_exists05
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_block_exists06
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_block_exists08
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_subblock_exists07_0
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_subblock_exists07_1
import Theorems.Thm_TaoFivePrimes_rh_high_height_count_from_finite_certificate
set_option Elab.async false
namespace RHFast256CountConditionalProof
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open scoped FourierTransform
namespace RHHighCountFromBlocks
lemma from_witnesses
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14)
 (b0 : RHHighContourBlocks.Block 0 1024 (109474726821181072649479699931489780124787:Int))
 (b1 : RHHighContourBlocks.Block 1024 1024 (109311968457341044839389112112005514116770:Int))
 (b2 : RHHighContourBlocks.Block 2048 1024 (109571840244712964494502534988015572730856:Int))
 (b3 : RHHighContourBlocks.Block 3072 1024 (109023063714152716956520007734775178844209:Int))
 (b4 : RHHighContourBlocks.Block 4096 1024 (95347179568355145696770173980499915190313:Int))
 (b5 : RHHighContourBlocks.Block 5120 1024 (109557364323034730827380755535190168203882:Int))
 (b6 : RHHighContourBlocks.Block 6144 1024 (109222057552147786244581392435653370580492:Int))
 (b7 : RHHighContourBlocks.Block 7168 1024 (109375781341265174060677403094527124681626:Int))
 (b8 : RHHighContourBlocks.Block 8192 256 (13581400043523159338086204868331027188070:Int))
 (hjet:∀e j k:Nat,e<4 → j≤RHHighContourGeometry.cells e → k<8 →
  ‖RHHighPolynomialJet.jet (RHHighContourGeometry.point e j) (RHHighContourGeometry.step e) k-
   RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12) :
 (RHHighHeight.windowZeros 3289999872 3290000000).ncard≤409 := by
 let a0:=b0
 let a1:=RHHighContourBlocks.append a0 b1
 let a2:=RHHighContourBlocks.append a1 b2
 let a3:=RHHighContourBlocks.append a2 b3
 let a4:=RHHighContourBlocks.append a3 b4
 let a5:=RHHighContourBlocks.append a4 b5
 let a6:=RHHighContourBlocks.append a5 b6
 let a7:=RHHighContourBlocks.append a6 b7
 let a8:=RHHighContourBlocks.append a7 b8
 have hlen:a8.records.length=8448:=a8.length_eq
 have hc:a8.records.zipIdx.all (fun p=>decide
  (p.1.edge=(if p.2<4096 then 0 else if p.2<4224 then 1 else if p.2<8320 then 2 else 3) ∧
   p.1.index=(if p.2<4096 then p.2 else if p.2<4224 then p.2-4096 else if p.2<8320 then p.2-4224 else p.2-8320)))=true := by
  change (a8.records.zipIdx).all RHHighContourBlocks.coordinates=true
  exact a8.coordinates_eq
 have hs:RHHighContourBlocks.signedTotal a8.records≤2571*(2:Int)^128 := by
  rw[a8.total_eq]
  norm_num
 have h0:0<b0.records.length:=by rw[b0.length_eq];norm_num
 exact TaoFivePrimes.rh_high_height_count_from_finite_certificate a8.records (b0.records[0]'h0)
  hlen hc hs hjet hcoeff
end RHHighCountFromBlocks
end
end RHFast256CountConditionalProof
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open scoped FourierTransform
theorem solution
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14)
 (hjet:∀e j k:Nat,e<4 → j≤RHHighContourGeometry.cells e → k<8 →
  ‖RHHighPolynomialJet.jet (RHHighContourGeometry.point e j) (RHHighContourGeometry.step e) k-
   RHHighContourVector.value (RHHighContourGridV2.jet e j k)‖≤1/10^12) :
 (RHHighHeight.windowZeros 3289999872 3290000000).ncard≤409 := by
 classical
 exact RHFast256CountConditionalProof.RHHighCountFromBlocks.from_witnesses hcoeff
  (Classical.choice TaoFivePrimes.rh_high_height_contour_block_exists00)
  (Classical.choice TaoFivePrimes.rh_high_height_contour_block_exists01)
  (Classical.choice TaoFivePrimes.rh_high_height_contour_block_exists02)
  (Classical.choice TaoFivePrimes.rh_high_height_contour_block_exists03)
  (Classical.choice TaoFivePrimes.rh_high_height_contour_block_exists04)
  (Classical.choice TaoFivePrimes.rh_high_height_contour_block_exists05)
  (Classical.choice TaoFivePrimes.rh_high_height_contour_block_exists06)
  (RHHighContourBlocks.append
   (Classical.choice TaoFivePrimes.rh_high_height_contour_subblock_exists07_0)
   (Classical.choice TaoFivePrimes.rh_high_height_contour_subblock_exists07_1))
  (Classical.choice TaoFivePrimes.rh_high_height_contour_block_exists08)
  hjet
#print axioms solution
