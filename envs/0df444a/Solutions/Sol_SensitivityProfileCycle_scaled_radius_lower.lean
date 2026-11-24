-- Prove2me | solution 1 for SensitivityProfileCycle.scaled_radius_lower
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-24T09:06:58.950346+00:00
-- url     : https://prove2.me/submissions/0f02050e-a81f-4702-b020-23b238c66065

import Definitions.Def_SensitivityProfileCycle
import Mathlib.Data.Finset.Max

/- The least diagonal product grows at every step of a profile cycle.
   The fixed-parameter argument of Prove2Me submission
   4b7c1dc7-bec0-4175-ad6c-0b721c44a55d uses the choices n=m=u=1.
   Keeping the tolerance in that coefficient, and using n=d+1 when all
   out-neighbors are allowed, makes the obstruction uniform in the data. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000

open SensitivityProfileCycle
open scoped Classical

private theorem cut_small (c : Certificate) (q : Fin c.toleranceCount)
    (hq : 0 < q.val) : 3 ≤ c.cutoffs q := by
  classical
  have hk : 2 ≤ (Finset.univ : Finset (Fin c.vertices)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact c.vertices_gt_one
  obtain ⟨I, _, hI⟩ := Finset.exists_subset_card_eq hk
  have h := c.defect q I (fun _ => 0) (by
    intro i hi
    have hlt : (I.filter (fun j => c.adj i j ∧ c.label i j ≠ 0)).card < I.card :=
      Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨i, hi, fun e => c.loopless i e.1⟩)
    omega)
  omega

private theorem cut_large (c : Certificate) (q : Fin c.toleranceCount)
    (hq : c.degree ≤ q.val) : c.vertices < c.cutoffs q := by
  classical
  have h := c.defect q Finset.univ (fun _ => 0) (by
    intro i _
    calc
      _ ≤ (Finset.univ.filter (c.adj i)).card := Finset.card_le_card
        (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩)
      _ = _ := c.outdegree i
      _ ≤ _ := hq)
  simpa using h

private theorem degree_lt (c : Certificate) : c.degree < c.vertices := by
  classical
  let i : Fin c.vertices := ⟨0, Nat.lt_trans Nat.zero_lt_one c.vertices_gt_one⟩
  have h := Finset.card_lt_card ((Finset.filter_ssubset (s := (Finset.univ : Finset (Fin c.vertices)))
    (p := c.adj i)).mpr ⟨i, Finset.mem_univ _, c.loopless i⟩)
  simpa [c.outdegree] using h

private theorem ordinary_forms (q v a b c e : ℕ) (hv : 3 ≤ v) :
    let L := a + (q+1)*c
    L ≤ coupledCost q v a b c e ∧
    L ≤ ordinaryCost q v a b c e ∧
    L ≤ ordinaryDedupInternalCost 2 q v a b c e := by
  dsimp only
  have hbudget : (1+1).choose 2 ≤ q*1+(q+1)*1 := by simp; omega
  have hol : ordinaryLimit q 1 1 = q+1 := by simp [ordinaryLimit]
  have hres : positiveResidual q 1 1 + 1 ≥ q+1 := by
    simp [positiveResidual, externalSlots]
  have hlim : dedupLimit q 1 1 1 = q+1 := by
    unfold dedupLimit
    rw [hol]
    apply Nat.min_eq_left
    simpa using hres
  have hcoef : min (dedupChoice q 1 1 1) (positiveResidual q 1 1+1) = q+1 := by
    unfold dedupChoice
    rw [hlim, Nat.min_eq_left hres, Nat.max_eq_right (by omega), Nat.min_eq_left hres]
  constructor
  · unfold coupledCost
    apply Finset.le_sup_of_le (b := 1) (by simp)
    apply Finset.le_sup_of_le (b := 1) (by simp)
    rw [if_pos hbudget]
    simp
  constructor
  · unfold ordinaryCost
    apply Finset.le_sup_of_le (b := 1) (by simp)
    apply Finset.le_sup_of_le (b := 1) (by simp)
    apply Finset.le_sup_of_le (b := 1) (by simp)
    rw [if_pos ⟨hbudget, by omega, le_rfl, by rw [hol]; omega⟩, hol]
    simp
  · unfold ordinaryDedupInternalCost dedupCost
    apply Finset.le_sup_of_le (b := 1) (by simp)
    apply Finset.le_sup_of_le (b := 1) (by simp)
    apply Finset.le_sup_of_le (b := 1) (by simp)
    rw [if_pos ⟨hbudget, by omega, le_rfl, by rw [hlim]; omega⟩, hcoef]
    simp only [Nat.one_mul]
    omega

private theorem source_forms (t w a b c e : ℕ) (hw : 3 ≤ w) :
    a+c ≤ sourceCost t w a b c e ∧ a+c ≤ strictSourceCost t w a b c e := by
  constructor
  · unfold sourceCost
    apply Finset.le_sup_of_le (b := 1) (by decide)
    apply Finset.le_sup_of_le (b := 1) (by decide)
    apply Finset.le_sup_of_le (b := 1) (by decide)
    have hcond : (1+1).choose 2 ≤ 1 ∧
        1+1 ≤ effectiveCutoff t w 1 1-1 ∧ (1:ℕ) ≤ 1 ∧ 1 ≤ ordinaryLimit 0 1 1 := by
      norm_num [effectiveCutoff, ordinaryLimit]
      omega
    rw [if_pos hcond]
    norm_num [effectiveCutoff, ordinaryLimit]
  · unfold strictSourceCost
    exact (Nat.le_add_right (a+c) ((w-3)*b)).trans
      ((le_max_left _ _).trans ((le_max_left _ _).trans
        ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))))

private theorem large_forms (q d v a b c e : ℕ) (hd : d ≤ q) (hv : d+1 < v) :
    let L := (d+1)*a
    L ≤ coupledCost q v a b c e ∧
    L ≤ ordinaryCost q v a b c e ∧
    L ≤ ordinaryDedupInternalCost 2 q v a b c e := by
  dsimp only
  have hm : d+1 < 2*q+2 := by omega
  have hb : (d+1+0).choose 2 ≤ q*(d+1)+(q+1)*0 := by
    simp only [Nat.add_zero, Nat.mul_zero, Nat.choose_two_right, Nat.add_sub_cancel]
    calc
      (d+1)*d/2 ≤ (d+1)*d := Nat.div_le_self _ _
      _ ≤ (d+1)*q := Nat.mul_le_mul_left _ hd
      _ = q*(d+1) := Nat.mul_comm _ _
  constructor
  · unfold coupledCost
    apply Finset.le_sup_of_le (b := d+1) (by simpa using hm)
    apply Finset.le_sup_of_le (b := 0) (by simp)
    rw [if_pos hb]
    omega
  constructor
  · unfold ordinaryCost
    apply Finset.le_sup_of_le (b := d+1) (by simpa using hm)
    apply Finset.le_sup_of_le (b := 0) (by simp)
    apply Finset.le_sup_of_le (b := 0) (by simp)
    rw [if_pos ⟨hb, by omega, le_rfl, Nat.zero_le _⟩]
    omega
  · unfold ordinaryDedupInternalCost dedupCost
    apply Finset.le_sup_of_le (b := d+1) (by simpa using hm)
    apply Finset.le_sup_of_le (b := 0) (by simp)
    apply Finset.le_sup_of_le (b := 0) (by simp)
    rw [if_pos ⟨hb, by omega, le_rfl, Nat.zero_le _⟩]
    omega

private theorem low_zero {n : ℕ} (C : Recipe n) (Z Y : Fin n → Fin n → ℕ)
    (K t w : ℕ) (v : ℕ → ℕ) (i : Fin n) (hi : 3 ≤ i.val)
    (hv : 3 ≤ v (C.tol i)) (hw : 3 ≤ w) :
    Z (C.target i) (C.target i) + (C.tol i+1)*Y (C.gate i) (C.gate i) ≤
      rawZeroSourceCombined K t v w C Z Y i i := by
  let a := Z (C.target i) (C.target i)
  let b := Z (C.gate i) (C.target i)
  let c := Y (C.gate i) (C.gate i)
  let e := Y (C.gate i) (C.target i)
  have hn : ¬i.val<3 := by omega
  obtain ⟨hc,ho,hd⟩ := ordinary_forms (C.tol i) (v (C.tol i)) a b c e hv
  by_cases hq : C.tol i=0
  · obtain ⟨hs,ht⟩ := source_forms t w a b c e hw
    have hmax : a+c ≤ max (max (max (max (a+c+(t-3)*b) (a+e+(t-2)*b))
        (c+e+(t-3)*b)) (2*e+(t-2)*b)) (3*e+(t-4)*b) :=
      le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
        (le_max_of_le_left (Nat.le_add_right _ _))))
    simp only [hq, Nat.zero_add, Nat.one_mul] at ho hd ⊢
    simpa only [rawZeroSourceCombined, rawZeroSourceFull, rawZeroSource, rawZeroOrdinary,
      rawZeroDedupBoth, rawZeroCoupled, hi, hn, hq, and_self, if_true, if_false,
      true_and, a, b, c, e] using
      (le_min (le_min (le_min (le_min hmax ho) hs) ht) (le_min hmax hd))
  · simpa only [rawZeroSourceCombined, rawZeroSourceFull, rawZeroSource, rawZeroOrdinary,
      rawZeroDedupBoth, rawZeroCoupled, hi, hn, hq, if_true, if_false, true_and,
      false_and, and_false, and_self, a, b, c, e] using
      (le_min (le_min hc ho) (le_min hc hd))

private theorem high_zero {n : ℕ} (C : Recipe n) (Z Y : Fin n → Fin n → ℕ)
    (K t w d : ℕ) (v : ℕ → ℕ) (i : Fin n) (hi : 3 ≤ i.val) (hq : 0 < C.tol i)
    (hd : d ≤ C.tol i) (hv : d+1 < v (C.tol i)) :
    (d+1)*Z (C.target i) (C.target i) ≤ rawZeroSourceCombined K t v w C Z Y i i := by
  have hn : ¬i.val<3 := by omega
  obtain ⟨hc,ho,hh⟩ := large_forms (C.tol i) d (v (C.tol i))
    (Z (C.target i) (C.target i)) (Z (C.gate i) (C.target i))
    (Y (C.gate i) (C.gate i)) (Y (C.gate i) (C.target i)) hd hv
  simpa only [rawZeroSourceCombined, rawZeroSourceFull, rawZeroSource, rawZeroOrdinary,
    rawZeroDedupBoth, rawZeroCoupled, hi, hn, Nat.ne_of_gt hq, if_true, if_false,
    true_and, false_and, and_false, and_self] using (le_min (le_min hc ho) (le_min hc hh))

private theorem product_amgm (M a c y z s d u v h : ℕ) (hay : M ≤ a*y) (hzc : M ≤ z*c)
    (hdom : d ≤ u*v) (hsq : h^2 ≤ 8*d*s^2) :
    (s*(d+2)+h)*M ≤ s*((a+u*c)*(2*y+v*z)) := by
  have hMM := Nat.mul_le_mul hay hzc
  have hcoef := hsq.trans (Nat.mul_le_mul_right (s^2) (Nat.mul_le_mul_left 8 hdom))
  have hcross2 : (h*M)^2 ≤ (s*v*a*z+s*2*u*c*y)^2 := calc
    _ = h^2*(M*M) := by ring
    _ ≤ (8*(u*v)*s^2)*((a*y)*(z*c)) := Nat.mul_le_mul hcoef hMM
    _ = 4*(s*v*a*z)*(s*2*u*c*y) := by ring
    _ ≤ _ := four_mul_le_sq_add _ _
  have hcross := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hcross2
  have hbase := Nat.mul_le_mul hdom hzc
  calc
    _ = s*(2*M+d*M)+h*M := by ring
    _ ≤ s*(2*(a*y)+(u*v)*(z*c))+(s*v*a*z+s*2*u*c*y) :=
      Nat.add_le_add (Nat.mul_le_mul_left s (Nat.add_le_add (Nat.mul_le_mul_left 2 hay) hbase)) hcross
    _ = _ := by ring

private theorem raw_product (C : Certificate) (d : Fin C.period) (M s B h : ℕ)
    (hK : B ≤ s*C.vertices) (hbig : B ≤ 2*s*(C.degree+1))
    (hsmall : B ≤ s*(C.degree+2)+h) (hsq : h^2 ≤ 8*C.degree*s^2)
    (hM : ∀ j, M ≤ C.zeroProfile d.castSucc j j*C.oneProfile d.castSucc j j)
    (i : Fin C.states) :
    B*M ≤ s*(C.zeroProfile d.succ i i*C.oneProfile d.succ i i) := by
  let r := C.recipe d
  let Z := C.zeroProfile d.castSucc
  let Y := C.oneProfile d.castSucc
  let v := extendCutoffs C.cutoffs
  let z' := rawZeroSourceCombined C.vertices C.ordinaryCutoff v C.sourceCutoff r Z Y i i
  let y' := rawOne C.degree r Z Y i i
  have hz' : z' ≤ C.zeroProfile d.succ i i := by
    obtain ⟨l,j,hl,hlj,hji,hb⟩ := C.zero_step d i i le_rfl
    have hli : l=i := le_antisymm (hlj.trans hji) hl
    have hji' : j=i := le_antisymm hji (hl.trans hlj)
    simpa [z',r,Z,Y,v,hli,hji'] using hb
  have hy' : y' ≤ C.oneProfile d.succ i i := by
    obtain ⟨l,j,hl,hlj,hji,hb⟩ := C.one_step d i i le_rfl
    have hli : l=i := le_antisymm (hlj.trans hji) hl
    have hji' : j=i := le_antisymm hji (hl.trans hlj)
    simpa [y',r,Z,Y,hli,hji'] using hb
  apply Nat.le_trans _ (Nat.mul_le_mul_left s (Nat.mul_le_mul hz' hy'))
  by_cases hi : i.val < 3
  · have hn : ¬3 ≤ i.val := by omega
    have haux : C.vertices*M ≤ z'*y' := by
      simp only [z',y',rawOne,rawZeroSourceCombined,rawZeroSourceFull,rawZeroSource,
        rawZeroOrdinary,rawZeroDedupBoth,rawZeroCoupled,hi,hn,false_and,if_true,if_false,min_self]
      have ht : M ≤ Z (r.target i) (r.target i) * Y (r.target i) (r.target i) := hM _
      have ht' := Nat.mul_le_mul_left C.vertices ht
      generalize r.aux i = e
      fin_cases e <;> norm_num [auxCost, Fin.ext_iff] <;> nlinarith only [ht']
    calc
      B*M ≤ (s*C.vertices)*M := Nat.mul_le_mul_right _ hK
      _ = s*(C.vertices*M) := Nat.mul_assoc _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ haux
  · have ho : 3 ≤ i.val := by omega
    let a := Z (r.target i) (r.target i)
    let c := Y (r.gate i) (r.gate i)
    let y := Y (r.target i) (r.target i)
    let z := Z (r.gate i) (r.gate i)
    let q := r.tol i
    have hay : M ≤ a*y := hM _
    have hzc : M ≤ z*c := hM _
    have hy : y' = 2*y + (C.degree-q)*z := by
      simp [y',rawOne,hi,y,z,q]
    by_cases hlarge : 0<q ∧ C.degree≤q
    · obtain ⟨hp,hd⟩ := hlarge
      have hqt : q<C.toleranceCount := C.tolerance_bound d i ho hp
      have hv : C.degree+1<v q := by
        have hgt := cut_large C ⟨q,hqt⟩ hd
        have hdeg := degree_lt C
        simp only [v,extendCutoffs,dif_pos hqt]
        omega
      have hzero : (C.degree+1)*a ≤ z' := high_zero _ _ _ _ _ _ _ _ _ ho hp hd hv
      have hone : 2*y ≤ y' := by rw [hy]; omega
      calc
        B*M ≤ (2*s*(C.degree+1))*(a*y) := Nat.mul_le_mul hbig hay
        _ = s*(((C.degree+1)*a)*(2*y)) := by ring
        _ ≤ _ := Nat.mul_le_mul_left s (Nat.mul_le_mul hzero hone)
    · have hv : 3 ≤ v q := by
        by_cases he : q=0
        · rw [he]
          change 3 ≤ extendCutoffs C.cutoffs 0
          rw [C.cutoff_zero]
          have := C.ordinary_ge_four
          omega
        · have hp : 0<q := Nat.pos_of_ne_zero he
          have hqt : q<C.toleranceCount := C.tolerance_bound d i ho hp
          simpa only [v,extendCutoffs,dif_pos hqt] using cut_small C ⟨q,hqt⟩ hp
      have hzero : a+(q+1)*c ≤ z' := low_zero _ _ _ _ _ _ _ _ ho hv (by have := C.source_ge_four; omega)
      have hdom : C.degree ≤ (q+1)*(C.degree-q) := by
        by_cases he : q=0
        · simp [he]
        · have hqd : q<C.degree := by omega
          have hrest : 1 ≤ C.degree-q := by omega
          have hh := Nat.mul_le_mul_left q hrest
          rw [Nat.mul_one] at hh
          rw [Nat.add_mul, Nat.one_mul]
          omega
      calc
        B*M ≤ (s*(C.degree+2)+h)*M := Nat.mul_le_mul_right _ hsmall
        _ ≤ s*((a+(q+1)*c)*(2*y+(C.degree-q)*z)) :=
          product_amgm M a c y z s _ _ _ h hay hzc hdom hsq
        _ ≤ s*(z'*y') := by
          rw [hy]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hzero)

theorem solution (C : SensitivityProfileCycle.Certificate) (s : ℕ) :
    (min (s*C.vertices) (min (2*s*(C.degree+1))
      (s*(C.degree+2)+Nat.sqrt (8*C.degree*s^2)))) ^ C.period ≤
      s ^ C.period * C.radius^2 := by
  classical
  let h := Nat.sqrt (8*C.degree*s^2)
  let B := min (s*C.vertices) (min (2*s*(C.degree+1)) (s*(C.degree+2)+h))
  have hK : B ≤ s*C.vertices := min_le_left _ _
  have hbig : B ≤ 2*s*(C.degree+1) := (min_le_right _ _).trans (min_le_left _ _)
  have hsmall : B ≤ s*(C.degree+2)+h := (min_le_right _ _).trans (min_le_right _ _)
  have hsq : h^2 ≤ 8*C.degree*s^2 := by rw [Nat.pow_two]; exact Nat.sqrt_le _
  let P (t : Fin (C.period+1)) (i : Fin C.states) := C.zeroProfile t i i*C.oneProfile t i i
  have pick (t : Fin (C.period+1)) : ∃ i, ∀ j, P t i ≤ P t j := by
    obtain ⟨i,_,hi⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin C.states)) (P t)
      ⟨C.output, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose best hbest using pick
  let m (t : Fin (C.period+1)) := P t (best t)
  have step (d : Fin C.period) : B*m d.castSucc ≤ s*m d.succ :=
    raw_product C d (m d.castSucc) s B h hK hbig hsmall hsq (hbest d.castSucc) (best d.succ)
  have chain (t : Fin (C.period+1)) : B ^ t.val * m 0 ≤ s ^ t.val * m t := by
    induction t using Fin.induction with
    | zero => simp
    | succ d ih =>
      simp only [Fin.val_succ, pow_succ]
      calc
        _ = B*(B ^ d.val * m 0) := by ring
        _ ≤ B*(s ^ d.val*m d.castSucc) := Nat.mul_le_mul_left _ ih
        _ = s ^ d.val*(B*m d.castSucc) := by ring
        _ ≤ s ^ d.val*(s*m d.succ) := Nat.mul_le_mul_left _ (step d)
        _ = _ := by ring
  have finish : m (Fin.last C.period) ≤ m 0 * C.radius^2 := calc
    _ ≤ P (Fin.last C.period) (best 0) := hbest _ _
    _ ≤ (C.zeroProfile 0 (best 0) (best 0)*C.radius)*
          (C.oneProfile 0 (best 0) (best 0)*C.radius) :=
      Nat.mul_le_mul (C.zero_cycle _ _ le_rfl) (C.one_cycle _ _ le_rfl)
    _ = m 0 * C.radius^2 := by dsimp [m,P]; ring
  have pos : 0 < m 0 := Nat.mul_pos (C.initial_positive _ _ le_rfl).1
    (C.initial_positive _ _ le_rfl).2
  apply Nat.le_of_mul_le_mul_right (c := m 0) _ pos
  change B^C.period*m 0 ≤ (s^C.period*C.radius^2)*m 0
  calc
    _ ≤ s^C.period*m (Fin.last C.period) := chain (Fin.last C.period)
    _ ≤ s^C.period*(m 0*C.radius^2) := Nat.mul_le_mul_left _ finish
    _ = _ := by ring
