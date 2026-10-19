-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_signs_from_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:27:30.78983+00:00
-- url     : https://prove2.me/submissions/5b79d826-c583-4e4c-98d7-dcf4988125e2

import Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface
import Definitions.Def_TaoFivePrimes_RHHighRealGrid
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_full_window_reconstruction
import Theorems.Thm_TaoFivePrimes_rh_high_height_real_grid_sign_checks
import Theorems.Thm_TaoFivePrimes_rh_high_height_real_polynomial_neg64
import Theorems.Thm_TaoFivePrimes_rh_high_height_real_polynomial_zero
import Theorems.Thm_TaoFivePrimes_rh_high_height_signs_from_real_grid
set_option Elab.async false
namespace RHFast256SignsConditionalProof
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RHHighFlatRows
lemma lookup {α : Type} (d : Nat) (hd:0< d) (a : α) (rows : List (List α))
    (hle:∀ r∈rows,r.length≤ d) (hfull:∀ r∈rows.dropLast,r.length=d)
    (i : Nat) (hi:i< rows.flatten.length) :
    ((rows.flatten[i]?).getD a)=((((rows[i/d]?).getD [])[i%d]?).getD a) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons xs xss ih =>
    cases xss with
    | nil =>
      have hx:xs.length≤ d:=hle xs (by simp)
      have hi':i< xs.length:=by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using hi
      have hid:i< d:=by omega
      simp only [List.flatten_cons,List.flatten_nil,List.append_nil,Nat.div_eq_of_lt hid,
        Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
    | cons ys yss =>
      have hx:xs.length=d:=hfull xs (by simp only [List.dropLast_cons_cons,List.mem_cons,true_or])
      have hle':∀ r∈ys::yss,r.length≤ d:=by intro r hr;exact hle r (List.mem_cons_of_mem _ hr)
      have hfull':∀ r∈(ys::yss).dropLast,r.length=d:=by
        intro r hr
        apply hfull r
        simp only [List.dropLast_cons_cons,List.mem_cons]
        exact Or.inr hr
      by_cases hid:i< d
      · rw [List.flatten_cons,List.getElem?_append_left (by omega),Nat.div_eq_of_lt hid,
          Nat.mod_eq_of_lt hid,List.getElem?_cons_zero,Option.getD_some]
      · have hdle:d≤ i:=by omega
        have he:i-d+d=i:=Nat.sub_add_cancel hdle
        have hdv:i/d=(i-d)/d+1 := by
          calc i/d=(i-d+d)/d:=by rw [he]
               _=(i-d)/d+1:=Nat.add_div_right _ hd
        have hmod:i%d=(i-d)%d := by
          calc i%d=(i-d+d)%d:=by rw [he]
               _=(i-d)%d:=Nat.add_mod_right _ _
        have hit:i-d<(ys::yss).flatten.length := by
          have hlen:(xs::ys::yss).flatten.length=d+(ys::yss).flatten.length:=by
            simp only [List.flatten_cons,List.length_append,hx]
          rw [hlen] at hi
          omega
        rw [List.flatten_cons,List.getElem?_append_right (by omega),hx,hdv,hmod,List.getElem?_cons_succ]
        exact ih hle' hfull' (i-d) hit
end RHHighFlatRows
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighFFTListInterface
noncomputable def entry (xs : List Nat) (j : Nat) : Nat := (xs[j]?).getD 0
lemma ofFn_at {N : Nat} (xs : List Nat) (h:xs.length=N) :
    List.ofFn (fun j:Fin N=>entry xs j.val)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,entry,List.getElem?_eq_getElem hj',Option.getD_some]
lemma bounded_at (xs : List Nat) (M : Nat)
    (h:xs.all (fun x=>decide (x≤M))=true) (j : Nat) : entry xs j≤M := by
  by_cases hj:j<xs.length
  · rw [entry,List.getElem?_eq_getElem hj,Option.getD_some]
    exact decide_eq_true_eq.mp ((List.all_eq_true.mp h) _ (List.getElem_mem hj))
  · have he:xs[j]?=none:=List.getElem?_eq_none (by omega)
    simp only [entry,he,Option.getD_none]
    exact Nat.zero_le _
lemma flatten_bounded (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.flatten.all (fun x=>decide (x≤M))=true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨row,hr,hx⟩:=List.mem_flatten.mp hx
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact (List.all_eq_true.mp hh.2) x hx
lemma uniform_lookup (rows : List (List Nat)) (i : Nat)
    (h:rows.all (fun row=>decide (row.length=512))=true)
    (hi:i<rows.flatten.length) :
    entry rows.flatten i=(((rows[i/512]?).getD [])[i%512]?).getD 0 := by
  unfold entry
  apply RHHighFlatRows.lookup 512 (by decide) 0 rows
  · intro row hr
    exact (decide_eq_true_eq.mp ((List.all_eq_true.mp h) row hr)).le
  · intro row hr
    apply decide_eq_true_eq.mp
    exact (List.all_eq_true.mp h) row (List.mem_of_mem_dropLast hr)
  · exact hi
lemma lengths_from_bound (rows : List (List Nat)) (M : Nat)
    (h:rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤M)))=true) :
    rows.all (fun row=>decide (row.length=512))=true := by
  apply List.all_eq_true.mpr
  intro row hr
  have hh:=(List.all_eq_true.mp h) row hr
  simp only [Bool.and_eq_true] at hh
  exact hh.1
end RHHighFFTListInterface
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex
namespace RHHighRealSigns
noncomputable def x (i : Nat) : ℝ := -64+(i:ℝ)/32
noncomputable def proposed (i : Nat) : ℝ := (RHHighRealGrid.value i:ℝ)/(2:ℝ)^80
lemma stable_opposite (a b u v : ℝ)
 (ha:1/10^8≤|a|) (hb:1/10^8≤|b|) (hab:a*b<0)
 (hu:|u-a|≤1/10^9) (hv:|v-b|≤1/10^9) : u*v<0 := by
 have hu':=abs_le.mp hu
 have hv':=abs_le.mp hv
 rcases mul_neg_iff.mp hab with ⟨ha0,hb0⟩|⟨ha0,hb0⟩
 · rw[abs_of_pos ha0] at ha
   rw[abs_of_neg hb0] at hb
   exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
 · rw[abs_of_neg ha0] at ha
   rw[abs_of_pos hb0] at hb
   exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
lemma W_real (u : ℝ) :
 (RHHighFullCoefficient.W u).re=RHHighHeight.normalized (u+3289999936)*Real.exp (-u^2/800) := by
 unfold RHHighFullCoefficient.W RHHighHeight.normalized RHHighHeight.normalizedComplex RHHighHeight.critical
 simp only[←Complex.ofReal_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
 rw[show -u^2/800=-(u^2/800) by ring,Real.exp_sub,Real.exp_neg]
 ring
lemma signs
 (hgrid:∀i:Nat,i<4096 → |(RHHighFullCoefficient.W (x i)).re-proposed i|≤1/10^9) :
 ∀p∈RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate,
 RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*
 RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0 := by
 intro p hp
 have h:=(List.all_eq_true.mp TaoFivePrimes.rh_high_height_real_grid_sign_checks) p hp
 simp only[decide_eq_true_eq] at h
 obtain ⟨hl,hr,hml,hmr,hs⟩:=h
 have margin (i : Nat) (hi:2^80≤10^8*(RHHighRealGrid.value i).natAbs) : 1/10^8≤|proposed i| := by
  have ht:(2:ℝ)^80≤10^8*|(RHHighRealGrid.value i:ℝ)| := by
   have h0:((2^80:Nat):ℝ)≤((10^8:Nat):ℝ)*((RHHighRealGrid.value i).natAbs:ℝ):=by exact_mod_cast hi
   simpa only[Nat.cast_pow,Nat.cast_ofNat,Nat.cast_natAbs,Int.cast_abs] using h0
  dsimp only[proposed]
  rw[abs_div,abs_of_pos (by positivity : (0:ℝ)<2^80)]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^80)).mpr
  linarith
 have hsign:proposed p.l*proposed p.r<0 := by
  dsimp only[proposed]
  rw[div_mul_div_comm]
  exact div_neg_of_neg_of_pos (by exact_mod_cast hs) (by positivity)
 have hv:=stable_opposite _ _ _ _ (margin p.l hml) (margin p.r hmr) hsign (hgrid p.l hl) (hgrid p.r hr)
 have point (i : Nat) : x i+3289999936=RHHighHeightBracketInterface.point i := by
  unfold x RHHighHeightBracketInterface.point
  ring
 rw[W_real,W_real,point,point] at hv
 have he:0< Real.exp (-(x p.l)^2/800)*Real.exp (-(x p.r)^2/800):=by positivity
 have hh:(RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*
  RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r))*
  (Real.exp (-(x p.l)^2/800)*Real.exp (-(x p.r)^2/800))<0 := by nlinarith only[hv]
 by_contra! hn
 exact (not_lt_of_ge (mul_nonneg hn he.le)) hh
end RHHighRealSigns
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
namespace RHHighRealGridSound
lemma left_shapes : RHHighContourOutputRealNeg64.rows.flatten.length=2048 ∧
 RHHighContourOutputRealNeg64.rows.all (fun row=> decide (row.length=512))=true := by decide +kernel
lemma zero_shapes : RHHighContourOutputRealZero.rows.flatten.length=2048 ∧
 RHHighContourOutputRealZero.rows.all (fun row=> decide (row.length=512))=true := by decide +kernel
lemma word_left (i : Nat) (hi:i<2048) : RHHighRealGrid.word i=
 (RHHighContourOutputRealNeg64.rows.flatten[i]?).getD 0 := by
 have h:=RHHighFFTListInterface.uniform_lookup RHHighContourOutputRealNeg64.rows i left_shapes.2
  (by rw[left_shapes.1];exact hi)
 simp only[RHHighRealGrid.word,RHHighRealGrid.outputRows,Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi,
  List.getElem?_cons_zero,Option.getD_some]
 exact h.symm
lemma word_zero (i : Nat) (hi:2048 ≤ i ∧ i<4096) : RHHighRealGrid.word i=
 (RHHighContourOutputRealZero.rows.flatten[i-2048]?).getD 0 := by
 have hj:i-2048<2048:=by omega
 have hd:i/2048=1:=by omega
 have hm:i%2048=i-2048:=by omega
 have hm512:i%512=(i-2048)%512:=by omega
 have h:=RHHighFFTListInterface.uniform_lookup RHHighContourOutputRealZero.rows (i-2048) zero_shapes.2
  (by rw[zero_shapes.1];exact hj)
 simp only[RHHighRealGrid.word,RHHighRealGrid.outputRows,hd,hm,hm512,
  List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
 exact h.symm
lemma polynomial
 (hl:∀j:Nat,j<2048 → ‖RHHighFourierPolynomial.polynomial (-64+(j:ℂ)/32)-
  RHHighContourVector.value (RHHighContourVector.decode ((RHHighContourOutputRealNeg64.rows.flatten[j]?).getD 0))‖≤1/10^12)
 (hz:∀j:Nat,j<2048 → ‖RHHighFourierPolynomial.polynomial (0+(j:ℂ)/32)-
  RHHighContourVector.value (RHHighContourVector.decode ((RHHighContourOutputRealZero.rows.flatten[j]?).getD 0))‖≤1/10^12)
 (i : Nat) (hi:i<4096) :
 ‖RHHighFourierPolynomial.polynomial (-64+(i:ℂ)/32)-
  RHHighContourVector.value (RHHighContourVector.decode (RHHighRealGrid.word i))‖≤1/10^12 := by
 by_cases hil:i<2048
 · rw[word_left i hil]
   exact hl i hil
 · rw[word_zero i ⟨by omega,hi⟩]
   have he:(i:ℂ)=((i-2048:Nat):ℂ)+2048:=by exact_mod_cast (Nat.sub_add_cancel (show 2048≤ i by omega)).symm
   have hx:(-64+(i:ℂ)/32)=(0+((i-2048:Nat):ℂ)/32):=by rw[he];ring
   rw[hx]
   exact hz (i-2048) (by omega)
lemma real_value (i : Nat) :
 (RHHighContourVector.value (RHHighContourVector.decode (RHHighRealGrid.word i))).re=RHHighRealSigns.proposed i := by
 unfold RHHighContourVector.value RHHighRealSigns.proposed RHHighRealGrid.value
 simp only[Complex.div_re,Complex.add_re,Complex.mul_re,Complex.intCast_re,Complex.intCast_im,
  Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero]
 norm_num
 ring
lemma window
 (hP:∀i:Nat,i<4096 → ‖RHHighFourierPolynomial.polynomial (-64+(i:ℂ)/32)-
  RHHighContourVector.value (RHHighContourVector.decode (RHHighRealGrid.word i))‖≤1/10^12)
 (hW:∀x:ℝ,|x|≤64 → ‖RHHighFullCoefficient.W x-RHHighFourierPolynomial.polynomial (x:ℂ)‖≤4/10^11)
 (i : Nat) (hi:i<4096) :
 |(RHHighFullCoefficient.W (RHHighRealSigns.x i)).re-RHHighRealSigns.proposed i|≤1/10^9 := by
 have hiR:(i:ℝ)≤4096:=by exact_mod_cast hi.le
 have hx:|RHHighRealSigns.x i|≤64 := by
  unfold RHHighRealSigns.x
  exact abs_le.mpr ⟨by linarith[Nat.cast_nonneg (α:=ℝ) i],by linarith⟩
 have hp:=hP i hi
 have hw:=hW _ hx
 have he:((RHHighRealSigns.x i:ℝ):ℂ)=-64+(i:ℂ)/32 := by unfold RHHighRealSigns.x;push_cast;rfl
 rw[he] at hw
 have h:=Complex.abs_re_le_norm (RHHighFullCoefficient.W (RHHighRealSigns.x i)-
  RHHighContourVector.value (RHHighContourVector.decode (RHHighRealGrid.word i)))
 simp only[Complex.sub_re,real_value] at h
 exact h.trans (((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hw hp)).trans (by norm_num))
end RHHighRealGridSound
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex
open scoped FourierTransform
namespace RHHighActualSigns
lemma signs
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14)
 (hl:∀j:Nat,j<2048 → ‖RHHighFourierPolynomial.polynomial (-64+(j:ℂ)/32)-
  RHHighContourVector.value (RHHighContourVector.decode ((RHHighContourOutputRealNeg64.rows.flatten[j]?).getD 0))‖≤1/10^12)
 (hz:∀j:Nat,j<2048 → ‖RHHighFourierPolynomial.polynomial (0+(j:ℂ)/32)-
  RHHighContourVector.value (RHHighContourVector.decode ((RHHighContourOutputRealZero.rows.flatten[j]?).getD 0))‖≤1/10^12) :
 ∀p∈RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate,
 RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0 := by
 apply TaoFivePrimes.rh_high_height_signs_from_real_grid
 have hP:=RHHighRealGridSound.polynomial hl hz
 have hW (x : ℝ) (hx:|x|≤64) : ‖RHHighFullCoefficient.W x-RHHighFourierPolynomial.polynomial (x:ℂ)‖≤4/10^11 := by
  have h:=TaoFivePrimes.rh_high_height_full_window_reconstruction 3289999936 x ⟨by norm_num,by norm_num⟩
   (hx.trans (by norm_num)) hcoeff
  exact h
 exact RHHighRealGridSound.window hP hW
end RHHighActualSigns
end
end RHFast256SignsConditionalProof
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open scoped FourierTransform
theorem solution
 (hcoeff:∀m:Nat,m≤1024 →
  ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-RHHighFourierPolynomial.coefficient m‖≤1/10^14)
 : ∀ p ∈ RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate, RHHighHeight.normalized (RHHighHeightBracketInterface.point p.l)*RHHighHeight.normalized (RHHighHeightBracketInterface.point p.r)<0 := by
 exact RHFast256SignsConditionalProof.RHHighActualSigns.signs
  hcoeff
  (fun j hj=>TaoFivePrimes.rh_high_height_real_polynomial_neg64 j hj)
  (fun j hj=>TaoFivePrimes.rh_high_height_real_polynomial_zero j hj)
#print axioms solution
