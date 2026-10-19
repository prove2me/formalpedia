-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_contour_reference_upper_zero_k06
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:18:15.431565+00:00
-- url     : https://prove2.me/submissions/ed781aa6-bd47-4c7b-9486-2107c37d8c0d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperZeroK06
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace RHBatch01LinearContourReferenceUpperZeroK06
open RHBatch01ContourCoefficientData RHBatch01ContourReference
noncomputable def input (p : Nat) (positive : Bool) : Int×Int :=
  let z:=RHBatch01ContourCoefficientData.decode p
  (z.1*2^48,(if positive then z.2 else -z.2)*2^48)
noncomputable def amp (r : Record) (positive : Bool) : Nat :=
  if positive then r.amplitude else r.inverse
noncomputable def freq (r : Record) (positive : Bool) : Int×Int :=
  (0,if positive then (r.x:Int) else -(r.x:Int))
noncomputable def seed (t : Fin 3) (positive : Bool) (r : Record) (p : Nat) : Int×Int :=
  mul (mul (input p positive) (RHHighContourUnit.pair (rootIndex t positive r.m))) ((amp r positive:Int),0)
noncomputable def reference (t : Fin 3) (positive : Bool) (r : Record) (p : Nat) : Nat→Int×Int
  | 0 => seed t positive r p
  | k+1 => divide (mul (reference t positive r p k) (freq r positive)) (k+1)
lemma reference_eq (t : Fin 3) (positive : Bool) (m : Nat) (hm:1 ≤ m ∧ m≤1024) (k : Nat) :
    reference t positive (lookup m) (RHBatch01FourierPolynomial.word m) k=
      coefficient t positive m k := by
  induction k with
  | zero =>
    simp only [reference,coefficient,seed,RHBatch01ContourCoefficientData.seed,input,inputCoefficient,
      RHBatch01ContourCoefficientData.decode,RHBatch01FourierPolynomial.realInteger,
      RHBatch01FourierPolynomial.imagInteger,amp,amplitude,lookup_m m hm]
  | succ k ih => rw [reference,coefficient,ih];rfl
noncomputable def check (t : Fin 3) (k : Nat) (rs : List Record) (ps ns ss : List Nat) : Bool :=
  (((rs.zip ps).zip ns).zip ss).all (fun q=>[false,true].all (fun positive=>
    let a:=reference t positive q.1.1.1 q.1.1.2 k
    let b:=RHBatch01ContourCoefficientData.decode (if positive then q.2 else q.1.2)
    decide (|a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)))
lemma sound (t : Fin 3) (k : Nat) (rs : List Record) (ps ns ss : List Nat)
    (hr:rs.length=16) (hp:ps.length=16) (hn:ns.length=16) (hs:ss.length=16)
    (hc:check t k rs ps ns ss=true) (j : Nat) (hj:j<16) (positive : Bool) :
    let a:=reference t positive rs[j] ps[j] k
    let b:=RHBatch01ContourCoefficientData.decode (if positive then ss[j] else ns[j])
    |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by
  have hjr:j<rs.length:=by omega
  have hjp:j<ps.length:=by omega
  have hjn:j<ns.length:=by omega
  have hjs:j<ss.length:=by omega
  have hm:(((rs[j],ps[j]),ns[j]),ss[j])∈((rs.zip ps).zip ns).zip ss := by
    apply List.mem_iff_getElem.mpr
    refine ⟨j,by simp only [List.length_zip,hr,hp,hn,hs];omega,?_⟩
    simp only [List.getElem_zip]
  have h:=(List.all_eq_true.mp hc) _ hm
  have hb:positive∈[false,true]:=by cases positive <;> simp
  exact of_decide_eq_true ((List.all_eq_true.mp h) positive hb)
end RHBatch01LinearContourReferenceUpperZeroK06
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace RHBatch01LinearContourReferenceUpperZeroK06
open RHBatch01ContourReference
lemma polynomial_row_lengths : RHBatch01ZetaFourierData.row00.length=512 ∧
    RHBatch01ZetaFourierData.row01.length=512 ∧ RHBatch01ZetaFourierData.row02.length=1 := by decide +kernel
lemma polynomial_flat_length : RHBatch01ZetaFourierData.rows.flatten.length=1025 := by decide +kernel
lemma records_length : RHBatch01ContourReference.records.length=1024 := by decide +kernel
lemma polynomial_word_flat (m : Nat) (hm:m<1025) :
    ((RHBatch01ZetaFourierData.rows.flatten[m]?).getD 0)=RHBatch01FourierPolynomial.word m := by
  have h0:=polynomial_row_lengths.1
  have h1:=polynomial_row_lengths.2.1
  have h2:=polynomial_row_lengths.2.2
  unfold RHBatch01FourierPolynomial.word
  change ((RHBatch01ZetaFourierData.row00++(RHBatch01ZetaFourierData.row01++RHBatch01ZetaFourierData.row02))[m]?).getD 0=
    ((([RHBatch01ZetaFourierData.row00,RHBatch01ZetaFourierData.row01,RHBatch01ZetaFourierData.row02][m/512]?).getD [])[m%512]?).getD 0
  by_cases hm0:m<512
  · have hd:m/512=0:=by omega
    have hr:m%512=m:=by omega
    rw [hd,hr,List.getElem?_cons_zero,Option.getD_some,List.getElem?_append_left (by omega)]
  · by_cases hm1:m<1024
    · have hd:m/512=1:=by omega
      have hr:m%512=m-512:=by omega
      rw [hd,hr,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
        List.getElem?_append_right (by omega),h0,List.getElem?_append_left (by omega)]
    · have he:m=1024:=by omega
      subst m
      decide +kernel
lemma slice_length {α : Type} (xs : List α) (lo : Nat) (hl:lo+16≤xs.length) :
    ((xs.drop lo).take 16).length=16 := by
  simp only [List.length_take,List.length_drop]
  omega
lemma slice_getD {α : Type} (xs : List α) (d : α) (lo j : Nat) (hj:j<16) :
    ((((xs.drop lo).take 16)[j]?).getD d)=(xs[lo+j]?).getD d := by
  rw [List.getElem?_take_of_lt hj,List.getElem?_drop]
lemma record_slice (c j : Nat) (hc:c<64) (hj:j<16) :
    ((((RHBatch01ContourReference.records.drop (16*c)).take 16)[j]?).getD record0001)=lookup (16*c+j+1) := by
  rw [slice_getD _ _ _ _ hj]
  simp only [lookup,Nat.add_sub_cancel]
lemma polynomial_slice (c j : Nat) (hc:c<64) (hj:j<16) :
    ((((RHBatch01ZetaFourierData.rows.flatten.drop (16*c+1)).take 16)[j]?).getD 0)=
      RHBatch01FourierPolynomial.word (16*c+j+1) := by
  rw [slice_getD _ _ _ _ hj]
  have he:16*c+1+j=16*c+j+1:=by omega
  rw [he]
  exact polynomial_word_flat _ (by omega)
end RHBatch01LinearContourReferenceUpperZeroK06

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHBatch01ContourLinearUpperZeroK06
open RHBatch01LinearContourReferenceUpperZeroK06 RHBatch01ContourReference RHBatch01ContourCoefficientData
noncomputable def values : List Nat := RHBatch01ContourSpectrumUpperZeroK06.rows.flatten
noncomputable def rs (c : Nat) := (RHBatch01ContourReference.records.drop (16*c)).take 16
noncomputable def ps (c : Nat) := (RHBatch01ZetaFourierData.rows.flatten.drop (16*c+1)).take 16
noncomputable def ns (c : Nat) := (values.drop (16*c+1)).take 16
noncomputable def ss (c : Nat) := (values.drop (16*c+1025)).take 16
theorem checked00 : check ⟨1,by decide⟩ 6 (rs 0) (ps 0) (ns 0) (ss 0)=true ∧ (rs 0).length=16 ∧ (ps 0).length=16 ∧ (ns 0).length=16 ∧ (ss 0).length=16 := by decide +kernel
theorem checked01 : check ⟨1,by decide⟩ 6 (rs 1) (ps 1) (ns 1) (ss 1)=true ∧ (rs 1).length=16 ∧ (ps 1).length=16 ∧ (ns 1).length=16 ∧ (ss 1).length=16 := by decide +kernel
theorem checked02 : check ⟨1,by decide⟩ 6 (rs 2) (ps 2) (ns 2) (ss 2)=true ∧ (rs 2).length=16 ∧ (ps 2).length=16 ∧ (ns 2).length=16 ∧ (ss 2).length=16 := by decide +kernel
theorem checked03 : check ⟨1,by decide⟩ 6 (rs 3) (ps 3) (ns 3) (ss 3)=true ∧ (rs 3).length=16 ∧ (ps 3).length=16 ∧ (ns 3).length=16 ∧ (ss 3).length=16 := by decide +kernel
theorem checked04 : check ⟨1,by decide⟩ 6 (rs 4) (ps 4) (ns 4) (ss 4)=true ∧ (rs 4).length=16 ∧ (ps 4).length=16 ∧ (ns 4).length=16 ∧ (ss 4).length=16 := by decide +kernel
theorem checked05 : check ⟨1,by decide⟩ 6 (rs 5) (ps 5) (ns 5) (ss 5)=true ∧ (rs 5).length=16 ∧ (ps 5).length=16 ∧ (ns 5).length=16 ∧ (ss 5).length=16 := by decide +kernel
theorem checked06 : check ⟨1,by decide⟩ 6 (rs 6) (ps 6) (ns 6) (ss 6)=true ∧ (rs 6).length=16 ∧ (ps 6).length=16 ∧ (ns 6).length=16 ∧ (ss 6).length=16 := by decide +kernel
theorem checked07 : check ⟨1,by decide⟩ 6 (rs 7) (ps 7) (ns 7) (ss 7)=true ∧ (rs 7).length=16 ∧ (ps 7).length=16 ∧ (ns 7).length=16 ∧ (ss 7).length=16 := by decide +kernel
theorem checked08 : check ⟨1,by decide⟩ 6 (rs 8) (ps 8) (ns 8) (ss 8)=true ∧ (rs 8).length=16 ∧ (ps 8).length=16 ∧ (ns 8).length=16 ∧ (ss 8).length=16 := by decide +kernel
theorem checked09 : check ⟨1,by decide⟩ 6 (rs 9) (ps 9) (ns 9) (ss 9)=true ∧ (rs 9).length=16 ∧ (ps 9).length=16 ∧ (ns 9).length=16 ∧ (ss 9).length=16 := by decide +kernel
theorem checked10 : check ⟨1,by decide⟩ 6 (rs 10) (ps 10) (ns 10) (ss 10)=true ∧ (rs 10).length=16 ∧ (ps 10).length=16 ∧ (ns 10).length=16 ∧ (ss 10).length=16 := by decide +kernel
theorem checked11 : check ⟨1,by decide⟩ 6 (rs 11) (ps 11) (ns 11) (ss 11)=true ∧ (rs 11).length=16 ∧ (ps 11).length=16 ∧ (ns 11).length=16 ∧ (ss 11).length=16 := by decide +kernel
theorem checked12 : check ⟨1,by decide⟩ 6 (rs 12) (ps 12) (ns 12) (ss 12)=true ∧ (rs 12).length=16 ∧ (ps 12).length=16 ∧ (ns 12).length=16 ∧ (ss 12).length=16 := by decide +kernel
theorem checked13 : check ⟨1,by decide⟩ 6 (rs 13) (ps 13) (ns 13) (ss 13)=true ∧ (rs 13).length=16 ∧ (ps 13).length=16 ∧ (ns 13).length=16 ∧ (ss 13).length=16 := by decide +kernel
theorem checked14 : check ⟨1,by decide⟩ 6 (rs 14) (ps 14) (ns 14) (ss 14)=true ∧ (rs 14).length=16 ∧ (ps 14).length=16 ∧ (ns 14).length=16 ∧ (ss 14).length=16 := by decide +kernel
theorem checked15 : check ⟨1,by decide⟩ 6 (rs 15) (ps 15) (ns 15) (ss 15)=true ∧ (rs 15).length=16 ∧ (ps 15).length=16 ∧ (ns 15).length=16 ∧ (ss 15).length=16 := by decide +kernel
theorem checked16 : check ⟨1,by decide⟩ 6 (rs 16) (ps 16) (ns 16) (ss 16)=true ∧ (rs 16).length=16 ∧ (ps 16).length=16 ∧ (ns 16).length=16 ∧ (ss 16).length=16 := by decide +kernel
theorem checked17 : check ⟨1,by decide⟩ 6 (rs 17) (ps 17) (ns 17) (ss 17)=true ∧ (rs 17).length=16 ∧ (ps 17).length=16 ∧ (ns 17).length=16 ∧ (ss 17).length=16 := by decide +kernel
theorem checked18 : check ⟨1,by decide⟩ 6 (rs 18) (ps 18) (ns 18) (ss 18)=true ∧ (rs 18).length=16 ∧ (ps 18).length=16 ∧ (ns 18).length=16 ∧ (ss 18).length=16 := by decide +kernel
theorem checked19 : check ⟨1,by decide⟩ 6 (rs 19) (ps 19) (ns 19) (ss 19)=true ∧ (rs 19).length=16 ∧ (ps 19).length=16 ∧ (ns 19).length=16 ∧ (ss 19).length=16 := by decide +kernel
theorem checked20 : check ⟨1,by decide⟩ 6 (rs 20) (ps 20) (ns 20) (ss 20)=true ∧ (rs 20).length=16 ∧ (ps 20).length=16 ∧ (ns 20).length=16 ∧ (ss 20).length=16 := by decide +kernel
theorem checked21 : check ⟨1,by decide⟩ 6 (rs 21) (ps 21) (ns 21) (ss 21)=true ∧ (rs 21).length=16 ∧ (ps 21).length=16 ∧ (ns 21).length=16 ∧ (ss 21).length=16 := by decide +kernel
theorem checked22 : check ⟨1,by decide⟩ 6 (rs 22) (ps 22) (ns 22) (ss 22)=true ∧ (rs 22).length=16 ∧ (ps 22).length=16 ∧ (ns 22).length=16 ∧ (ss 22).length=16 := by decide +kernel
theorem checked23 : check ⟨1,by decide⟩ 6 (rs 23) (ps 23) (ns 23) (ss 23)=true ∧ (rs 23).length=16 ∧ (ps 23).length=16 ∧ (ns 23).length=16 ∧ (ss 23).length=16 := by decide +kernel
theorem checked24 : check ⟨1,by decide⟩ 6 (rs 24) (ps 24) (ns 24) (ss 24)=true ∧ (rs 24).length=16 ∧ (ps 24).length=16 ∧ (ns 24).length=16 ∧ (ss 24).length=16 := by decide +kernel
theorem checked25 : check ⟨1,by decide⟩ 6 (rs 25) (ps 25) (ns 25) (ss 25)=true ∧ (rs 25).length=16 ∧ (ps 25).length=16 ∧ (ns 25).length=16 ∧ (ss 25).length=16 := by decide +kernel
theorem checked26 : check ⟨1,by decide⟩ 6 (rs 26) (ps 26) (ns 26) (ss 26)=true ∧ (rs 26).length=16 ∧ (ps 26).length=16 ∧ (ns 26).length=16 ∧ (ss 26).length=16 := by decide +kernel
theorem checked27 : check ⟨1,by decide⟩ 6 (rs 27) (ps 27) (ns 27) (ss 27)=true ∧ (rs 27).length=16 ∧ (ps 27).length=16 ∧ (ns 27).length=16 ∧ (ss 27).length=16 := by decide +kernel
theorem checked28 : check ⟨1,by decide⟩ 6 (rs 28) (ps 28) (ns 28) (ss 28)=true ∧ (rs 28).length=16 ∧ (ps 28).length=16 ∧ (ns 28).length=16 ∧ (ss 28).length=16 := by decide +kernel
theorem checked29 : check ⟨1,by decide⟩ 6 (rs 29) (ps 29) (ns 29) (ss 29)=true ∧ (rs 29).length=16 ∧ (ps 29).length=16 ∧ (ns 29).length=16 ∧ (ss 29).length=16 := by decide +kernel
theorem checked30 : check ⟨1,by decide⟩ 6 (rs 30) (ps 30) (ns 30) (ss 30)=true ∧ (rs 30).length=16 ∧ (ps 30).length=16 ∧ (ns 30).length=16 ∧ (ss 30).length=16 := by decide +kernel
theorem checked31 : check ⟨1,by decide⟩ 6 (rs 31) (ps 31) (ns 31) (ss 31)=true ∧ (rs 31).length=16 ∧ (ps 31).length=16 ∧ (ns 31).length=16 ∧ (ss 31).length=16 := by decide +kernel
theorem checked32 : check ⟨1,by decide⟩ 6 (rs 32) (ps 32) (ns 32) (ss 32)=true ∧ (rs 32).length=16 ∧ (ps 32).length=16 ∧ (ns 32).length=16 ∧ (ss 32).length=16 := by decide +kernel
theorem checked33 : check ⟨1,by decide⟩ 6 (rs 33) (ps 33) (ns 33) (ss 33)=true ∧ (rs 33).length=16 ∧ (ps 33).length=16 ∧ (ns 33).length=16 ∧ (ss 33).length=16 := by decide +kernel
theorem checked34 : check ⟨1,by decide⟩ 6 (rs 34) (ps 34) (ns 34) (ss 34)=true ∧ (rs 34).length=16 ∧ (ps 34).length=16 ∧ (ns 34).length=16 ∧ (ss 34).length=16 := by decide +kernel
theorem checked35 : check ⟨1,by decide⟩ 6 (rs 35) (ps 35) (ns 35) (ss 35)=true ∧ (rs 35).length=16 ∧ (ps 35).length=16 ∧ (ns 35).length=16 ∧ (ss 35).length=16 := by decide +kernel
theorem checked36 : check ⟨1,by decide⟩ 6 (rs 36) (ps 36) (ns 36) (ss 36)=true ∧ (rs 36).length=16 ∧ (ps 36).length=16 ∧ (ns 36).length=16 ∧ (ss 36).length=16 := by decide +kernel
theorem checked37 : check ⟨1,by decide⟩ 6 (rs 37) (ps 37) (ns 37) (ss 37)=true ∧ (rs 37).length=16 ∧ (ps 37).length=16 ∧ (ns 37).length=16 ∧ (ss 37).length=16 := by decide +kernel
theorem checked38 : check ⟨1,by decide⟩ 6 (rs 38) (ps 38) (ns 38) (ss 38)=true ∧ (rs 38).length=16 ∧ (ps 38).length=16 ∧ (ns 38).length=16 ∧ (ss 38).length=16 := by decide +kernel
theorem checked39 : check ⟨1,by decide⟩ 6 (rs 39) (ps 39) (ns 39) (ss 39)=true ∧ (rs 39).length=16 ∧ (ps 39).length=16 ∧ (ns 39).length=16 ∧ (ss 39).length=16 := by decide +kernel
theorem checked40 : check ⟨1,by decide⟩ 6 (rs 40) (ps 40) (ns 40) (ss 40)=true ∧ (rs 40).length=16 ∧ (ps 40).length=16 ∧ (ns 40).length=16 ∧ (ss 40).length=16 := by decide +kernel
theorem checked41 : check ⟨1,by decide⟩ 6 (rs 41) (ps 41) (ns 41) (ss 41)=true ∧ (rs 41).length=16 ∧ (ps 41).length=16 ∧ (ns 41).length=16 ∧ (ss 41).length=16 := by decide +kernel
theorem checked42 : check ⟨1,by decide⟩ 6 (rs 42) (ps 42) (ns 42) (ss 42)=true ∧ (rs 42).length=16 ∧ (ps 42).length=16 ∧ (ns 42).length=16 ∧ (ss 42).length=16 := by decide +kernel
theorem checked43 : check ⟨1,by decide⟩ 6 (rs 43) (ps 43) (ns 43) (ss 43)=true ∧ (rs 43).length=16 ∧ (ps 43).length=16 ∧ (ns 43).length=16 ∧ (ss 43).length=16 := by decide +kernel
theorem checked44 : check ⟨1,by decide⟩ 6 (rs 44) (ps 44) (ns 44) (ss 44)=true ∧ (rs 44).length=16 ∧ (ps 44).length=16 ∧ (ns 44).length=16 ∧ (ss 44).length=16 := by decide +kernel
theorem checked45 : check ⟨1,by decide⟩ 6 (rs 45) (ps 45) (ns 45) (ss 45)=true ∧ (rs 45).length=16 ∧ (ps 45).length=16 ∧ (ns 45).length=16 ∧ (ss 45).length=16 := by decide +kernel
theorem checked46 : check ⟨1,by decide⟩ 6 (rs 46) (ps 46) (ns 46) (ss 46)=true ∧ (rs 46).length=16 ∧ (ps 46).length=16 ∧ (ns 46).length=16 ∧ (ss 46).length=16 := by decide +kernel
theorem checked47 : check ⟨1,by decide⟩ 6 (rs 47) (ps 47) (ns 47) (ss 47)=true ∧ (rs 47).length=16 ∧ (ps 47).length=16 ∧ (ns 47).length=16 ∧ (ss 47).length=16 := by decide +kernel
theorem checked48 : check ⟨1,by decide⟩ 6 (rs 48) (ps 48) (ns 48) (ss 48)=true ∧ (rs 48).length=16 ∧ (ps 48).length=16 ∧ (ns 48).length=16 ∧ (ss 48).length=16 := by decide +kernel
theorem checked49 : check ⟨1,by decide⟩ 6 (rs 49) (ps 49) (ns 49) (ss 49)=true ∧ (rs 49).length=16 ∧ (ps 49).length=16 ∧ (ns 49).length=16 ∧ (ss 49).length=16 := by decide +kernel
theorem checked50 : check ⟨1,by decide⟩ 6 (rs 50) (ps 50) (ns 50) (ss 50)=true ∧ (rs 50).length=16 ∧ (ps 50).length=16 ∧ (ns 50).length=16 ∧ (ss 50).length=16 := by decide +kernel
theorem checked51 : check ⟨1,by decide⟩ 6 (rs 51) (ps 51) (ns 51) (ss 51)=true ∧ (rs 51).length=16 ∧ (ps 51).length=16 ∧ (ns 51).length=16 ∧ (ss 51).length=16 := by decide +kernel
theorem checked52 : check ⟨1,by decide⟩ 6 (rs 52) (ps 52) (ns 52) (ss 52)=true ∧ (rs 52).length=16 ∧ (ps 52).length=16 ∧ (ns 52).length=16 ∧ (ss 52).length=16 := by decide +kernel
theorem checked53 : check ⟨1,by decide⟩ 6 (rs 53) (ps 53) (ns 53) (ss 53)=true ∧ (rs 53).length=16 ∧ (ps 53).length=16 ∧ (ns 53).length=16 ∧ (ss 53).length=16 := by decide +kernel
theorem checked54 : check ⟨1,by decide⟩ 6 (rs 54) (ps 54) (ns 54) (ss 54)=true ∧ (rs 54).length=16 ∧ (ps 54).length=16 ∧ (ns 54).length=16 ∧ (ss 54).length=16 := by decide +kernel
theorem checked55 : check ⟨1,by decide⟩ 6 (rs 55) (ps 55) (ns 55) (ss 55)=true ∧ (rs 55).length=16 ∧ (ps 55).length=16 ∧ (ns 55).length=16 ∧ (ss 55).length=16 := by decide +kernel
theorem checked56 : check ⟨1,by decide⟩ 6 (rs 56) (ps 56) (ns 56) (ss 56)=true ∧ (rs 56).length=16 ∧ (ps 56).length=16 ∧ (ns 56).length=16 ∧ (ss 56).length=16 := by decide +kernel
theorem checked57 : check ⟨1,by decide⟩ 6 (rs 57) (ps 57) (ns 57) (ss 57)=true ∧ (rs 57).length=16 ∧ (ps 57).length=16 ∧ (ns 57).length=16 ∧ (ss 57).length=16 := by decide +kernel
theorem checked58 : check ⟨1,by decide⟩ 6 (rs 58) (ps 58) (ns 58) (ss 58)=true ∧ (rs 58).length=16 ∧ (ps 58).length=16 ∧ (ns 58).length=16 ∧ (ss 58).length=16 := by decide +kernel
theorem checked59 : check ⟨1,by decide⟩ 6 (rs 59) (ps 59) (ns 59) (ss 59)=true ∧ (rs 59).length=16 ∧ (ps 59).length=16 ∧ (ns 59).length=16 ∧ (ss 59).length=16 := by decide +kernel
theorem checked60 : check ⟨1,by decide⟩ 6 (rs 60) (ps 60) (ns 60) (ss 60)=true ∧ (rs 60).length=16 ∧ (ps 60).length=16 ∧ (ns 60).length=16 ∧ (ss 60).length=16 := by decide +kernel
theorem checked61 : check ⟨1,by decide⟩ 6 (rs 61) (ps 61) (ns 61) (ss 61)=true ∧ (rs 61).length=16 ∧ (ps 61).length=16 ∧ (ns 61).length=16 ∧ (ss 61).length=16 := by decide +kernel
theorem checked62 : check ⟨1,by decide⟩ 6 (rs 62) (ps 62) (ns 62) (ss 62)=true ∧ (rs 62).length=16 ∧ (ps 62).length=16 ∧ (ns 62).length=16 ∧ (ss 62).length=16 := by decide +kernel
theorem checked63 : check ⟨1,by decide⟩ 6 (rs 63) (ps 63) (ns 63) (ss 63)=true ∧ (rs 63).length=16 ∧ (ps 63).length=16 ∧ (ns 63).length=16 ∧ (ss 63).length=16 := by decide +kernel
lemma chunks (c : Nat) (hc:c<64) : check ⟨1,by decide⟩ 6 (rs c) (ps c) (ns c) (ss c)=true ∧ (rs c).length=16 ∧ (ps c).length=16 ∧ (ns c).length=16 ∧ (ss c).length=16 := by
  interval_cases c
  · exact checked00
  · exact checked01
  · exact checked02
  · exact checked03
  · exact checked04
  · exact checked05
  · exact checked06
  · exact checked07
  · exact checked08
  · exact checked09
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31
  · exact checked32
  · exact checked33
  · exact checked34
  · exact checked35
  · exact checked36
  · exact checked37
  · exact checked38
  · exact checked39
  · exact checked40
  · exact checked41
  · exact checked42
  · exact checked43
  · exact checked44
  · exact checked45
  · exact checked46
  · exact checked47
  · exact checked48
  · exact checked49
  · exact checked50
  · exact checked51
  · exact checked52
  · exact checked53
  · exact checked54
  · exact checked55
  · exact checked56
  · exact checked57
  · exact checked58
  · exact checked59
  · exact checked60
  · exact checked61
  · exact checked62
  · exact checked63
lemma row_sound (c j : Nat) (hc:c<64) (hj:j<16) (positive : Bool) :
    let m:=16*c+j+1
    let a:=coefficient ⟨1,by decide⟩ positive m 6
    let b:=proposed values positive m
    |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by
  have q:=chunks c hc
  have hr:=q.2.1
  have hp:=q.2.2.1
  have hn:=q.2.2.2.1
  have hs:=q.2.2.2.2
  have h:=sound ⟨1,by decide⟩ 6 (rs c) (ps c) (ns c) (ss c) hr hp hn hs q.1 j hj positive
  have hrs:(rs c)[j]'(by omega)=lookup (16*c+j+1) := by
    have h0:=record_slice c j hc hj
    change (((rs c)[j]?).getD record0001)=_ at h0
    rw [List.getElem?_eq_getElem (by omega),Option.getD_some] at h0
    exact h0
  have hps:(ps c)[j]'(by omega)=RHBatch01FourierPolynomial.word (16*c+j+1) := by
    have h0:=polynomial_slice c j hc hj
    change (((ps c)[j]?).getD 0)=_ at h0
    rw [List.getElem?_eq_getElem (by omega),Option.getD_some] at h0
    exact h0
  have hns:(ns c)[j]'(by omega)=(values[16*c+j+1]?).getD 0 := by
    have h0:=slice_getD values 0 (16*c+1) j hj
    change (((ns c)[j]?).getD 0)=_ at h0
    rw [List.getElem?_eq_getElem (by omega),Option.getD_some,
      show 16*c+1+j=16*c+j+1 by omega] at h0
    exact h0
  have hss:(ss c)[j]'(by omega)=(values[1024+(16*c+j+1)]?).getD 0 := by
    have h0:=slice_getD values 0 (16*c+1025) j hj
    change (((ss c)[j]?).getD 0)=_ at h0
    rw [List.getElem?_eq_getElem (by omega),Option.getD_some,
      show 16*c+1025+j=1024+(16*c+j+1) by omega] at h0
    exact h0
  rw [hrs,hps,reference_eq ⟨1,by decide⟩ positive (16*c+j+1) (by constructor <;> omega) 6,hns,hss] at h
  cases positive <;> simpa only [proposed,Bool.false_eq_true,if_false,if_true] using h
lemma checked (m : Nat) (hm:1 ≤ m ∧ m≤1024) (positive : Bool) :
    let a:=coefficient ⟨1,by decide⟩ positive m 6
    let b:=proposed values positive m
    |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by
  have h:=row_sound ((m-1)/16) ((m-1)%16) (by omega) (Nat.mod_lt _ (by decide)) positive
  have he:16*((m-1)/16)+(m-1)%16+1=m:=by omega
  simpa only [he] using h
end RHBatch01ContourLinearUpperZeroK06
theorem solution :
  ∀ m:Nat,1 ≤ m ∧ m≤1024 → ∀ positive:Bool,
  let a:=RHBatch01ContourCoefficientData.coefficient ⟨1,by decide⟩ positive m 6
  let b:=RHBatch01ContourCoefficientData.proposed RHBatch01ContourSpectrumUpperZeroK06.rows.flatten positive m
  |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by
  exact RHBatch01ContourLinearUpperZeroK06.checked
#print axioms solution
