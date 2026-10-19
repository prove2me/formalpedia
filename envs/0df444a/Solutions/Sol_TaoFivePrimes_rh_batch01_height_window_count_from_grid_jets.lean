-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_window_count_from_grid_jets
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T18:14:26.010979+00:00
-- url     : https://prove2.me/submissions/68cd3432-5e52-407a-8d20-44fb83d8b7f5

import Definitions.Def_TaoFivePrimes_RHBatch01ContourBlocks
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_count_from_finite_certificate
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_full_coefficient_enclosure
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness00
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness01
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness02
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness03
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness04
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness05
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness06
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness07
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness08
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness09
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness10
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness11
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness12
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness13
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness14
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness15
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_witness16
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace RHBatch01CountFromBlocks
lemma from_witnesses
 (b0 : RHBatch01ContourBlocks.Block 0 1024 (109662139940117391116027348976616120377379:Int))
 (b1 : RHBatch01ContourBlocks.Block 1024 1024 (109144618679546071156031319352849028858090:Int))
 (b2 : RHBatch01ContourBlocks.Block 2048 1024 (109598131601686205536023891600268808038186:Int))
 (b3 : RHBatch01ContourBlocks.Block 3072 1024 (108943465067167250411897482131448096226870:Int))
 (b4 : RHBatch01ContourBlocks.Block 4096 1024 (95559445476710890108306006596800110867079:Int))
 (b5 : RHBatch01ContourBlocks.Block 5120 1024 (109836413513774223324958148759222654434546:Int))
 (b6 : RHBatch01ContourBlocks.Block 6144 1024 (108835331440291621638244563514114262113306:Int))
 (b7 : RHBatch01ContourBlocks.Block 7168 1024 (109737837003595394155617861950809970186576:Int))
 (b8 : RHBatch01ContourBlocks.Block 8192 256 (13147999343296383484738856993823837899670:Int))
 (hjet:∀e j k:Nat,e<4 → j≤RHBatch01ContourGeometry.cells e → k<8 →
  ‖RHBatch01PolynomialJet.jet (RHBatch01ContourGeometry.point e j) (RHBatch01ContourGeometry.step e) k-
   RHHighContourVector.value (RHBatch01ContourGridV2.jet e j k)‖≤1/10^12) :
 (RHHighHeight.windowZeros 3289999744 3289999872).ncard≤409 := by
 let a0:=b0
 let a1:=RHBatch01ContourBlocks.append a0 b1
 let a2:=RHBatch01ContourBlocks.append a1 b2
 let a3:=RHBatch01ContourBlocks.append a2 b3
 let a4:=RHBatch01ContourBlocks.append a3 b4
 let a5:=RHBatch01ContourBlocks.append a4 b5
 let a6:=RHBatch01ContourBlocks.append a5 b6
 let a7:=RHBatch01ContourBlocks.append a6 b7
 let a8:=RHBatch01ContourBlocks.append a7 b8
 have hlen:a8.records.length=8448:=a8.length_eq
 have hc:a8.records.zipIdx.all (fun p=>decide
  (p.1.edge=(if p.2<4096 then 0 else if p.2<4224 then 1 else if p.2<8320 then 2 else 3) ∧
   p.1.index=(if p.2<4096 then p.2 else if p.2<4224 then p.2-4096 else if p.2<8320 then p.2-4224 else p.2-8320)))=true := by
  change (a8.records.zipIdx).all RHBatch01ContourBlocks.coordinates=true
  exact a8.coordinates_eq
 have hs:RHBatch01ContourBlocks.signedTotal a8.records≤2571*(2:Int)^128 := by
  rw[a8.total_eq]
  norm_num
 have h0:0<b0.records.length:=by rw[b0.length_eq];norm_num
 exact TaoFivePrimes.rh_batch01_height_count_from_finite_certificate a8.records (b0.records[0]'h0)
  hlen hc hs hjet (fun n hn=>TaoFivePrimes.rh_batch01_height_full_coefficient_enclosure n hn)
end RHBatch01CountFromBlocks
theorem solution
 (hjet:∀e j k:Nat,e<4 → j≤RHBatch01ContourGeometry.cells e → k<8 →
  ‖RHBatch01PolynomialJet.jet (RHBatch01ContourGeometry.point e j) (RHBatch01ContourGeometry.step e) k-
   RHHighContourVector.value (RHBatch01ContourGridV2.jet e j k)‖≤1/10^12) :
 (RHHighHeight.windowZeros 3289999744 3289999872).ncard≤409 := by
 classical
 exact RHBatch01CountFromBlocks.from_witnesses
  (RHBatch01ContourBlocks.append (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness00) (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness01))
  (RHBatch01ContourBlocks.append (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness02) (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness03))
  (RHBatch01ContourBlocks.append (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness04) (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness05))
  (RHBatch01ContourBlocks.append (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness06) (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness07))
  (RHBatch01ContourBlocks.append (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness08) (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness09))
  (RHBatch01ContourBlocks.append (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness10) (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness11))
  (RHBatch01ContourBlocks.append (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness12) (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness13))
  (RHBatch01ContourBlocks.append (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness14) (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness15))
  (Classical.choice TaoFivePrimes.rh_batch01_height_contour_witness16)
  hjet
#print axioms solution
