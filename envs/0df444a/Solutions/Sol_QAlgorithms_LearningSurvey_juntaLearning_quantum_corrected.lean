-- Prove2me | solution 1 for QAlgorithms.LearningSurvey.juntaLearning_quantum_corrected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:38:11.842009+00:00
-- url     : https://prove2.me/submissions/3f5c5326-f021-4acd-9a6b-0f5259b55ad0

import Definitions.Def_QAlgorithms_LearningSurvey_Ch05_Model
import Theorems.Thm_QAlgorithms_LearningSurvey_junta_quantum_selector
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

open scoped BigOperators
open Finset QAlgorithms QAlgorithms.LearningSurvey

namespace JuntaTable
noncomputable def avg {X : Type*} [Fintype X] (g : X → ℝ) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * ∑ x, g x

lemma avg_nonneg {X : Type*} [Fintype X] (g : X → ℝ) (h : ∀ x, 0 ≤ g x) :
    0 ≤ avg g := mul_nonneg (by positivity) (sum_nonneg fun x _ => h x)

lemma avg_mono {X : Type*} [Fintype X] {g h : X → ℝ} (H : ∀ x, g x ≤ h x) :
    avg g ≤ avg h := mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => H x) (by positivity)

lemma avg_add {X : Type*} [Fintype X] (g h : X → ℝ) :
    avg (fun x => g x + h x) = avg g + avg h := by simp [avg, sum_add_distrib, mul_add]

lemma avg_mul {X : Type*} [Fintype X] (c : ℝ) (g : X → ℝ) :
    avg (fun x => c * g x) = c * avg g := by
  unfold avg
  rw [← mul_sum]
  ring

lemma avg_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    avg (fun _ : X => c) = c := by
  have h : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [avg, h]

lemma avg_comm {X Y : Type*} [Fintype X] [Fintype Y] (g : X → Y → ℝ) :
    avg (fun x => avg (g x)) = avg (fun y => avg (fun x => g x y)) := by
  simp only [avg, ← mul_sum]
  rw [sum_comm];ring

lemma avg_fin_succ {X : Type*} [Fintype X] (T : ℕ) (g : (Fin (T+1) → X) → ℝ) :
    avg g = avg (fun x => avg (fun xs : Fin T → X => g (Fin.cons x xs))) := by
  classical
  unfold avg
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (T+1) => X), Fintype.sum_prod_type]
  simp only [Fintype.card_fun, Fintype.card_fin, pow_succ,
    Nat.cast_mul, mul_inv_rev, ← mul_sum]
  rw [mul_assoc]
  rfl

noncomputable def predict {X : Type*} (R : X → X → Prop) [DecidableRel R]
    {T : ℕ} (xs : Fin T → X) (f : X → Bool) (x : X) : Bool :=
  match (List.finRange T).find? (fun j => decide (R (xs j) x)) with
  | some j => f (xs j)
  | none => false

lemma predict_zero {X : Type*} (R : X → X → Prop) [DecidableRel R]
    (xs : Fin 0 → X) (f : X → Bool) (x : X) : predict R xs f x = false := by
  simp [predict]

lemma predict_cons {X : Type*} (R : X → X → Prop) [DecidableRel R] {T : ℕ}
    (y : X) (xs : Fin T → X) (f : X → Bool) (x : X) :
    predict R (Fin.cons y xs) f x = if R y x then f y else predict R xs f x := by
  classical
  simp only [predict, List.finRange_succ, List.find?_cons, Fin.cons_zero]
  split_ifs with h
  · simp [h]
  · simp only [h, decide_false, List.find?_map,
      Function.comp_def, Fin.cons_succ]
    cases (List.finRange T).find? (fun j => decide (R (xs j) x)) <;> rfl

lemma point_error {X : Type*} [Fintype X] [Nonempty X]
    (R : X → X → Prop) [DecidableRel R] (f : X → Bool) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hmass : ∀ x, avg (fun y => if R y x then (1:ℝ) else 0) = p)
    (T : ℕ) (x : X) :
    avg (fun xs : Fin T → X => if predict R xs f x ≠ f x then (1:ℝ) else 0) ≤
      avg (fun y => if R y x ∧ f y ≠ f x then (1:ℝ) else 0) / p + (1-p)^T := by
  classical
  let q := avg (fun y => if R y x ∧ f y ≠ f x then (1:ℝ) else 0)
  have hq : 0 ≤ q := avg_nonneg _ (by intro; positivity)
  induction T with
  | zero =>
    simpa only [predict_zero, pow_zero] using
      (le_trans (avg_mono (fun _ => show (if false ≠ f x then (1:ℝ) else 0) ≤ 1 by split_ifs <;> norm_num))
        (by rw [avg_const]; exact le_add_of_nonneg_left (div_nonneg hq hp.le)))
  | succ T ih =>
    rw [avg_fin_succ]
    have hid (y : X) (xs : Fin T → X) :
        (if predict R (Fin.cons y xs) f x ≠ f x then (1:ℝ) else 0) =
        (if R y x ∧ f y ≠ f x then (1:ℝ) else 0) +
        (if R y x then (0:ℝ) else 1) * (if predict R xs f x ≠ f x then (1:ℝ) else 0) := by
      rw [predict_cons];split_ifs <;> simp_all
    simp_rw [hid, avg_add, avg_const, avg_mul]
    simp_rw [mul_comm (ite (R _ x) (0:ℝ) 1)]
    rw [avg_mul]
    rw [mul_comm (avg _) (avg _)]
    have hmiss : avg (fun y => if R y x then (0:ℝ) else 1) = 1-p := by
      rw [← hmass x, ← avg_const (X:=X) 1]
      unfold avg
      rw [← mul_sub, ← sum_sub_distrib]
      congr 1;apply sum_congr rfl;intro y _;split_ifs <;> simp_all
    rw [hmiss]
    calc
      q + (1-p) * avg (fun xs : Fin T → X => if predict R xs f x ≠ f x then (1:ℝ) else 0)
          ≤ q + (1-p) * (q/p+(1-p)^T) := by gcongr
      _ = q/p + (1-p)^(T+1) := by rw [pow_succ]; field_simp [hp.ne']; ring

end JuntaTable

namespace JuntaTable

lemma mask_mass {n : ℕ} (V : Fin n → Bool) (x : Qubits n) :
    avg (fun y : Qubits n => if (∀ i, V i = true → y i = x i) then (1:ℝ) else 0) =
      ((2:ℝ)^hammingWeight V)⁻¹ := by
  classical
  let E : {y : Qubits n // ∀ i, V i = true → y i = x i} ≃ ({i : Fin n // V i = false} → Bool) :=
    { toFun := fun y i => y.1 i.1
      invFun := fun g => ⟨fun i => if h : V i = true then x i else g ⟨i, by cases hi : V i <;> simp_all⟩,
        by intro i hi; simp [hi]⟩
      left_inv := by
        intro y;apply Subtype.ext;funext i
        dsimp only
        split_ifs with h
        · exact (y.2 i h).symm
        · rfl
      right_inv := by intro g; funext i;simp [i.2] }
  have hc : Fintype.card {i : Fin n // V i = false} + hammingWeight V = n := by
    have h := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (p:=fun i : Fin n => V i = true)
    have hf : (Finset.univ.filter fun i : Fin n => ¬ V i = true) =
        (Finset.univ.filter fun i => V i = false) := by
      ext i; simp only [mem_filter, mem_univ, true_and]; cases V i <;> decide
    rw [hf] at h
    simpa only [hammingWeight, Fintype.card_subtype, Finset.card_univ, Fintype.card_fin, add_comm] using h
  have hn : (Fintype.card (Qubits n) : ℝ) = 2^n := by
    simp [Qubits]
  have hcard : (∑ y : Qubits n, if (∀ i, V i = true → y i = x i) then (1:ℝ) else 0) =
      (2:ℝ)^Fintype.card {i : Fin n // V i = false} := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Fintype.card_subtype]
    rw [Fintype.card_congr E, Fintype.card_fun]
    norm_num
  rw [avg, hn, hcard]
  have he : (2:ℝ)^n = 2^Fintype.card {i : Fin n // V i = false} * 2^hammingWeight V := by
    rw [← pow_add, hc]
  rw [he]
  field_simp

lemma table_expected_error {n T : ℕ} (V : Fin n → Bool) (f : Qubits n → Bool) :
    avg (fun xs : Fin T → Qubits n =>
      Learning.pacError (Learning.uniformDist (Qubits n)) f (tableHypothesis V xs f)) ≤
    avg (fun x : Qubits n =>
      avg (fun y : Qubits n => if (∀ i, V i = true → y i = x i) ∧ f y ≠ f x then (1:ℝ) else 0) *
        (2:ℝ)^hammingWeight V) + (1-((2:ℝ)^hammingWeight V)⁻¹)^T := by
  classical
  have hp : 0 < ((2:ℝ)^hammingWeight V)⁻¹ := by positivity
  have hp1 : ((2:ℝ)^hammingWeight V)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have heq (xs : Fin T → Qubits n) :
      Learning.pacError (Learning.uniformDist (Qubits n)) f (tableHypothesis V xs f) =
        avg (fun x => if predict (fun y x : Qubits n => ∀ i, V i = true → y i = x i) xs f x ≠ f x
          then (1:ℝ) else 0) := by
    unfold Learning.pacError Learning.uniformDist avg
    rw [Finset.sum_filter, Finset.mul_sum]
    apply sum_congr rfl;intro x _
    change (if predict (fun y x : Qubits n => ∀ i, V i = true → y i = x i) xs f x ≠ f x then _ else 0) = _
    split_ifs <;> simp_all
  simp_rw [heq]
  rw [avg_comm]
  calc
    _ ≤ avg (fun x : Qubits n =>
      avg (fun y : Qubits n => if (∀ i, V i = true → y i = x i) ∧ f y ≠ f x then (1:ℝ) else 0) /
        ((2:ℝ)^hammingWeight V)⁻¹ + (1-((2:ℝ)^hammingWeight V)⁻¹)^T) :=
      avg_mono (fun x => point_error _ f _ hp hp1 (mask_mass V) T x)
    _ = _ := by simp only [div_inv_eq_mul, avg_add, avg_const]

end JuntaTable


open Finset QAlgorithms QAlgorithms.LearningSurvey JuntaTable

namespace JuntaReduction

lemma avg_sub {X : Type*} [Fintype X] (g h : X → ℝ) :
    avg (fun x => g x - h x) = avg g - avg h := by
  simp only [avg, sum_sub_distrib, mul_sub]

lemma markov {X : Type*} [Fintype X] [Nonempty X] (e : X → ℝ)
    (he : ∀ x, 0 ≤ e x) (ε : ℝ) :
    ε * (1 - avg (fun x => if e x ≤ ε then (1:ℝ) else 0)) ≤ avg e := by
  calc
    _ = avg (fun x => ε * (1 - if e x ≤ ε then (1:ℝ) else 0)) := by
      rw [avg_mul, avg_sub, avg_const]
    _ ≤ _ := avg_mono (fun x => by split_ifs with h <;> simp only [sub_self, sub_zero, mul_zero, mul_one]; exact he x; exact (not_le.mp h).le)

lemma sample_avg {n T : ℕ} (g : (Fin T → Qubits n) → ℝ) :
    avg g = (((2:ℝ)^n)^T)⁻¹ * ∑ xs, g xs := by
  simp [avg, Qubits]

lemma error_nonneg {n : ℕ} (f h : Qubits n → Bool) :
    0 ≤ Learning.pacError (Learning.uniformDist (Qubits n)) f h := by
  unfold Learning.pacError Learning.uniformDist
  positivity

lemma success_bound {n k : ℕ} (L : JuntaHybridLearner n) (f : Qubits n → Bool)
    (ε η : ℝ) (hε : 0 < ε) (hcap : ∀ z, hammingWeight (L.post.eval z) ≤ k)
    (hnorm : (∑ z, prob (act L.circ.unitary (juntaExamplesState n L.TQ L.anc f)) z) = 1)
    (hD : (∑ z, prob (act L.circ.unitary (juntaExamplesState n L.TQ L.anc f)) z *
      avg (fun x : Qubits n => avg (fun y : Qubits n =>
        if (∀ i, L.post.eval z i = true → y i = x i) ∧ f y ≠ f x then (1:ℝ) else 0) *
          (2:ℝ)^hammingWeight (L.post.eval z))) ≤ η)
    (htail : (1-((2:ℝ)^k)⁻¹)^L.TC ≤ η) :
    ε * (1-L.successProb f ε) ≤ 2*η := by
  classical
  let P := fun z => prob (act L.circ.unitary (juntaExamplesState n L.TQ L.anc f)) z
  let E := fun z (xs : Fin L.TC → Qubits n) =>
    Learning.pacError (Learning.uniformDist (Qubits n)) f (tableHypothesis (L.post.eval z) xs f)
  have hP z : 0 ≤ P z := by exact sq_nonneg _
  have hm z := markov (E z) (fun xs => error_nonneg _ _) ε
  have hw := sum_le_sum (s:=Finset.univ) (fun z _ => mul_le_mul_of_nonneg_left (hm z) (hP z))
  have hleft : (∑ z, P z * (ε * (1-avg (fun xs => if E z xs ≤ ε then (1:ℝ) else 0)))) =
      ε * (1-L.successProb f ε) := by
    simp_rw [mul_sub, mul_one, mul_left_comm (P _) ε]
    rw [sum_sub_distrib, ← sum_mul, ← mul_sum, hnorm]
    simp only [JuntaHybridLearner.successProb, ← sample_avg]
    ring
  rw [hleft] at hw
  apply hw.trans
  have he z := table_expected_error (T:=L.TC) (L.post.eval z) f
  have ht z : (1-((2:ℝ)^hammingWeight (L.post.eval z))⁻¹)^L.TC ≤ (1-((2:ℝ)^k)⁻¹)^L.TC := by
    apply pow_le_pow_left₀
    · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
    · apply sub_le_sub_left
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (hcap z))
  calc
    (∑ z, P z * avg (E z)) ≤ ∑ z, P z *
        (avg (fun x : Qubits n => avg (fun y : Qubits n =>
          if (∀ i, L.post.eval z i = true → y i = x i) ∧ f y ≠ f x then (1:ℝ) else 0) *
            (2:ℝ)^hammingWeight (L.post.eval z)) + (1-((2:ℝ)^k)⁻¹)^L.TC) := by
      exact sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (he z |>.trans (add_le_add_right (ht z) _)) (hP z)
    _ ≤ 2*η := by
      simp only [mul_add, sum_add_distrib, ← sum_mul]
      rw [hnorm];linarith

lemma tail_bound (k T : ℕ) (a : ℝ) (ha : 0 < a) (hT : (2:ℝ)^k * Real.log (1/a) ≤ T) :
    (1-((2:ℝ)^k)⁻¹)^T ≤ a := by
  have hb : 0 ≤ 1-((2:ℝ)^k)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  calc
    _ ≤ (Real.exp (-((2:ℝ)^k)⁻¹))^T := pow_le_pow_left₀ hb (by linarith [Real.add_one_le_exp (-((2:ℝ)^k)⁻¹)]) T
    _ = Real.exp (-((T:ℝ)/(2:ℝ)^k)) := by rw [← Real.exp_nat_mul];congr 1;ring
    _ ≤ Real.exp (-Real.log (1/a)) := Real.exp_le_exp.mpr (by apply neg_le_neg; exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hT))
    _ = a := by rw [Real.exp_neg, Real.exp_log (by positivity)];simp

end JuntaReduction

open JuntaReduction in
theorem solution :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, 2 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∃ L : JuntaHybridLearner n,
          (L.TQ : ℝ) ≤ C * ((k : ℝ) * Real.log k / ε) ∧
          (L.TC : ℝ) ≤ C * ((2 : ℝ) ^ k * Real.log (1 / ε)) ∧
          (L.cost : ℝ) ≤ C * ((n : ℝ) * k * Real.log k / ε + (2 : ℝ) ^ k * Real.log (1 / ε)) ∧
          ∀ f : Qubits n → Bool, IsJunta f k → L.successProb f ε ≥ 1 - δ := by
  classical
  intro δ hδ hδ1
  obtain ⟨A,hA,hselector⟩ := junta_quantum_selector
  let q := 2*A/δ
  let b := Real.log (2/δ)
  let B := 1+(b+1)/Real.log 2
  let C := 1+q+B+1/Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < b := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hq : 0 < q := by dsimp [q]; positivity
  have hB : 0 < B := by dsimp [B];positivity
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro n k hk hkn ε hε hε1
  let η := δ*ε/2
  have hη : 0 < η := by dsimp [η];positivity
  have hη1 : η ≤ 1/2 := by dsimp [η];nlinarith
  obtain ⟨L,hTC,hTQ,hstage,hcap,hprob⟩ := hselector n k hk hkn η hη hη1
  let T := Nat.ceil ((2:ℝ)^k * Real.log (1/η))
  let L' : JuntaHybridLearner n := { L with TC := T }
  have hT : (2:ℝ)^k * Real.log (1/η) ≤ T := Nat.le_ceil _
  have hTupper : (T:ℝ) ≤ (2:ℝ)^k * Real.log (1/η)+1 := (Nat.ceil_lt_add_one (by
    apply mul_nonneg (by positivity); apply Real.log_nonneg; exact (le_div_iff₀ hη).mpr (by linarith))).le
  let l := Real.log (1/ε)
  have hl : Real.log 2 ≤ l := Real.log_le_log (by norm_num) ((le_div_iff₀ hε).mpr (by linarith))
  have hl0 : 0 < l := hlog2.trans_le hl
  have hpow : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hlog : Real.log (1/η) = b+l := by
    have hid : 1/η = (2/δ)*(1/ε) := by dsimp [η];field_simp
    rw [hid, Real.log_mul (by positivity) (by positivity)]
  have hTB : (T:ℝ) ≤ B*((2:ℝ)^k*l) := by
    rw [hlog] at hTupper
    have hh : b+1 ≤ ((b+1)/Real.log 2)*l := by
      have hh' : (b+1)*Real.log 2 ≤ (b+1)*l := by nlinarith
      calc
        b+1 ≤ (b+1)*l/Real.log 2 := (le_div_iff₀ hlog2).mpr hh'
        _ = _ := by ring
    have hhpow := mul_le_mul_of_nonneg_left hh (show 0 ≤ (2:ℝ)^k by positivity)
    dsimp [B]
    nlinarith
  have hTQ' : (L.TQ:ℝ) ≤ q*((k:ℝ)*Real.log k/ε) := by
    convert hTQ using 1
    dsimp [q,η]
    field_simp
  have hstage' : ((L.circ.size+(L.TQ*(n+1)+L.anc)+L.post.size:ℕ):ℝ) ≤
      q*((n:ℝ)*k*Real.log k/ε) := by
    convert hstage using 1
    dsimp [q,η]
    field_simp
  have hK : 0 ≤ (k:ℝ)*Real.log k/ε := by
    apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega)))) hε.le
  have hN : 0 ≤ (n:ℝ)*k*Real.log k/ε := by
    simpa only [mul_div_assoc, ← mul_assoc] using mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) hK
  have hcell : (2:ℝ)^k ≤ (1/Real.log 2)*((2:ℝ)^k*l) := by
    have hh : 1 ≤ l/Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hl)
    have hhpow := mul_le_mul_of_nonneg_left hh (show 0 ≤ (2:ℝ)^k by positivity)
    calc
      (2:ℝ)^k = (2:ℝ)^k*1 := by ring
      _ ≤ (2:ℝ)^k*(l/Real.log 2) := hhpow
      _ = _ := by ring
  have hcost : (L'.cost:ℝ) ≤ q*((n:ℝ)*k*Real.log k/ε)+B*((2:ℝ)^k*l)+(1/Real.log 2)*((2:ℝ)^k*l) := by
    have hsup : (Finset.univ.sup fun z => 2^hammingWeight (L.post.eval z)) ≤ 2^k :=
      Finset.sup_le (fun z _ => Nat.pow_le_pow_right (by omega) (hcap z))
    have hsup' : ((Finset.univ.sup (fun z => (2:ℕ)^hammingWeight (L.post.eval z)) : ℕ) : ℝ) ≤ (2:ℝ)^k := by exact_mod_cast hsup
    change ((L.circ.size+(L.TQ*(n+1)+L.anc)+L.post.size+T+
      Finset.univ.sup (fun z => 2^hammingWeight (L.post.eval z)):ℕ):ℝ) ≤ _
    push_cast
    push_cast at hstage'
    linarith
  refine ⟨L',?_,?_,?_,?_⟩
  · change (L.TQ:ℝ) ≤ _
    apply hTQ'.trans
    apply mul_le_mul_of_nonneg_right _ hK
    dsimp [C];linarith [show 0 < 1/Real.log 2 by positivity]
  · change (T:ℝ) ≤ _
    apply hTB.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ (2:ℝ)^k*l)
    dsimp [C];linarith [show 0 < 1/Real.log 2 by positivity]
  · apply hcost.trans
    have hqC : q ≤ C := by dsimp [C]; linarith [show 0 < 1/Real.log 2 by positivity]
    have hBC : B+1/Real.log 2 ≤ C := by dsimp [C];linarith
    have h1 := mul_le_mul_of_nonneg_right hqC hN
    have h2 := mul_le_mul_of_nonneg_right hBC (show 0 ≤ (2:ℝ)^k*l by positivity)
    dsimp [l] at h2
    nlinarith
  · intro f hf
    obtain ⟨hnorm,hD⟩ := hprob f hf
    have hD' : (∑ z, prob (act L'.circ.unitary (juntaExamplesState n L'.TQ L'.anc f)) z *
      avg (fun x : Qubits n => avg (fun y : Qubits n =>
        if (∀ i, L'.post.eval z i = true → y i = x i) ∧ f y ≠ f x then (1:ℝ) else 0) *
        (2:ℝ)^hammingWeight (L'.post.eval z))) ≤ η := by
      simpa only [L',avg,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat,Qubits] using hD
    have htail : (1-((2:ℝ)^k)⁻¹)^L'.TC ≤ η := tail_bound k T η hη hT
    have H := success_bound L' f ε η hε hcap hnorm hD' htail
    dsimp [η] at H
    nlinarith
