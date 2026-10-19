-- Prove2me | solution 1 for QAlgorithms.Arunachalam.pgm_pac_hard_ensemble
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:58:03.509934+00:00
-- url     : https://prove2.me/submissions/b79c21ce-9a53-4b68-bf46-a3a0dffb6bfd

import Theorems.Thm_QAlgorithms_pgmSuccess_uniform_real_gram
import Theorems.Thm_QAlgorithms_Arunachalam_sqrtA_diag
import Theorems.Thm_QAlgorithms_Arunachalam_fourier_weightPow_bound
import Mathlib.Analysis.Complex.Exponential
set_option autoImplicit false
open scoped BigOperators
open QAlgorithms QAlgorithms.Learning

private lemma sqrt_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs := Finset.sum_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hi := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hp := mul_nonneg (Real.sqrt_nonneg (f a)) (Real.sqrt_nonneg (∑ i ∈ s, f i))
    have h := Real.sq_sqrt (add_nonneg (hf a (Finset.mem_insert_self _ _)) hs)
    have h1 := Real.sq_sqrt (hf a (Finset.mem_insert_self _ _))
    have h2 := Real.sq_sqrt hs
    have hr := Real.sqrt_nonneg (f a + ∑ i ∈ s, f i)
    have h3 := Real.sqrt_nonneg (f a)
    have h4 := Real.sqrt_nonneg (∑ i ∈ s, f i)
    nlinarith

private lemma sum_weight (m : ℕ) (t : ℝ) :
    (∑ S : Fin m → ZMod 2, t ^ hammingNorm S) = (1+t)^m := by
  classical
  have point (S : Fin m → ZMod 2) :
      t ^ hammingNorm S = ∏ i, if S i ≠ 0 then t else 1 := by
    simp [Finset.prod_ite, hammingNorm]
  simp_rw [point]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (z : ZMod 2) => if z ≠ 0 then t else 1)]
  have bit : (∑ z : ZMod 2, if z ≠ 0 then t else 1) = 1+t := by
    change (∑ z : Fin 2, if (z : ZMod 2) ≠ 0 then t else 1) = _
    simp [Fin.sum_univ_succ]
  simp_rw [bit]
  simp

private lemma fiber_sqrt_le {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    (f : (Fin m → ZMod 2) → ℝ) (hf : ∀ S, 0 ≤ f S) :
    (∑ Q : Fin k → ZMod 2, Real.sqrt
      (∑ S ∈ Finset.univ.filter (fun S => M.transpose.mulVec S = Q), f S)) ≤
      ∑ S, Real.sqrt (f S) := by
  classical
  calc
    _ ≤ ∑ Q : Fin k → ZMod 2,
        ∑ S ∈ Finset.univ.filter (fun S => M.transpose.mulVec S = Q), Real.sqrt (f S) := by
      apply Finset.sum_le_sum
      intro Q _
      exact sqrt_sum_le _ _ (fun S _ => hf S)
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      simp

private lemma sqrt_pow (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Real.sqrt (t^n) = (Real.sqrt t)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ht _), ih, pow_succ]

private lemma diag_bound {m k T : ℕ} {β : ℝ} (hm : 10 ≤ m) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hT : 1 ≤ T) (hTm : (T : ℝ) ≤ (m : ℝ) / (Real.exp 3 * β)) (hk : k ≤ m)
    (M : Matrix (Fin m) (Fin k) (ZMod 2)) (hM : M.rank = k) (x : Fin k → ZMod 2) :
    (psdSqrt (xorConvMatrix fun z => weightPowFun m β T (M.mulVec z)) x x)^2 ≤
      ((2:ℝ)^k)⁻¹ * (4*Real.exp 1*(1-β/2)^T) *
        Real.exp (22*(T:ℝ)^2*β^2/(m:ℝ) + 2*Real.sqrt ((T:ℝ)*(m:ℝ)*β)) := by
  classical
  let t := (T:ℝ)*β/(m:ℝ)
  let K := 4*Real.exp 1*(1-β/2)^T*Real.exp (22*(T:ℝ)^2*β^2/(m:ℝ))
  let U := ∑ Q : Fin k → ZMod 2, Real.sqrt
    (∑ S ∈ Finset.univ.filter (fun S : Fin m → ZMod 2 => M.transpose.mulVec S = Q),
      boolFourier (weightPowFun m β T) S)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hK : 0 ≤ K := by
    have : 0 ≤ 1-β/2 := by linarith
    dsimp [K]
    positivity
  have hb := QAlgorithms.Arunachalam.fourier_weightPow_bound hm hβ hβ1 hT hTm
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hsum : U ≤ Real.sqrt K * (1+Real.sqrt t)^m := by
    calc
      U ≤ ∑ S, Real.sqrt (boolFourier (weightPowFun m β T) S) :=
        fiber_sqrt_le M _ (fun S => (hb S).1)
      _ ≤ ∑ S : Fin m → ZMod 2, Real.sqrt K * (Real.sqrt t)^hammingNorm S := by
        apply Finset.sum_le_sum
        intro S _
        calc
          _ ≤ Real.sqrt (K*t^hammingNorm S) := Real.sqrt_le_sqrt (by
            dsimp [K,t]; nlinarith only [(hb S).2])
          _ = _ := by rw [Real.sqrt_mul hK, sqrt_pow t ht]
      _ = _ := by rw [← Finset.mul_sum, sum_weight]
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have heq : (m:ℝ)*Real.sqrt t = Real.sqrt ((T:ℝ)*(m:ℝ)*β) := by
    calc
      _ = Real.sqrt ((m:ℝ)^2) * Real.sqrt t := by rw [Real.sqrt_sq hm0.le]
      _ = Real.sqrt ((m:ℝ)^2*t) := (Real.sqrt_mul (sq_nonneg _) _).symm
      _ = _ := by congr 1; dsimp [t]; field_simp
  have he : (1+Real.sqrt t)^m ≤ Real.exp (Real.sqrt ((T:ℝ)*(m:ℝ)*β)) := by
    calc
      _ ≤ (Real.exp (Real.sqrt t))^m :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (Real.sqrt t)]) _
      _ = _ := by rw [← Real.exp_nat_mul, heq]
  have hu : U ≤ Real.sqrt K * Real.exp (Real.sqrt ((T:ℝ)*(m:ℝ)*β)) :=
    hsum.trans (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _))
  rw [QAlgorithms.Arunachalam.sqrtA_diag hm hβ hβ1 hT hTm hk M hM x]
  change ((Real.sqrt ((2:ℝ)^k))⁻¹ * U)^2 ≤ _
  have hu2 : U^2 ≤ K * Real.exp (2*Real.sqrt ((T:ℝ)*(m:ℝ)*β)) := by
    calc
      _ ≤ (Real.sqrt K * Real.exp (Real.sqrt ((T:ℝ)*(m:ℝ)*β)))^2 :=
        pow_le_pow_left₀ hU hu 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hK, ← Real.exp_nat_mul]; norm_num
  calc
    _ = ((2:ℝ)^k)⁻¹ * U^2 := by rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    _ ≤ ((2:ℝ)^k)⁻¹ * (K * Real.exp (2*Real.sqrt ((T:ℝ)*(m:ℝ)*β))) :=
      mul_le_mul_of_nonneg_left hu2 (by positivity)
    _ = _ := by dsimp [K]; rw [Real.exp_add]; ring

private lemma tensor_inner {ι : Type*} [Fintype ι] (T : ℕ)
    (u v : EuclideanSpace ℂ ι) :
    inner ℂ (tensorPow T u) (tensorPow T v) = (inner ℂ u v)^T := by
  simp only [PiLp.inner_apply, tensorPow, RCLike.inner_apply, map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin T) (i : ι) => v i * (starRingEnd ℂ) (u i))]
  simp

private lemma example_inner {X : Type*} [Fintype X] (c e : X → Bool) (D : X → ℝ)
    (hD : ∀ i, 0 ≤ D i) :
    inner ℂ (exampleState c D) (exampleState e D) =
      ((∑ i, if c i = e i then D i else 0 : ℝ) : ℂ) := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  cases hc : c i <;> cases he : e i <;>
    simp [exampleState, hc, he, abs_of_nonneg (Real.sqrt_nonneg _),
      ← Complex.ofReal_pow, Real.sq_sqrt (hD i)]

private lemma bit_eq {d k : ℕ} (M : Matrix (Fin d) (Fin k) (ZMod 2))
    (x y : Fin k → ZMod 2) (i : Fin d) :
    codeConcept M x i = codeConcept M y i ↔ (M.mulVec (x+y)) i = 0 := by
  rw [Matrix.mulVec_add]
  simp only [Pi.add_apply, codeConcept, decide_eq_decide]
  have hb (a b : ZMod 2) : (a = 1 ↔ b = 1) ↔ a+b = 0 := by
    have bits (z : ZMod 2) : z = 0 ∨ z = 1 := by
      have h : z.val = 0 ∨ z.val = 1 := by have := ZMod.val_lt z; omega
      rcases h with h | h
      · exact Or.inl ((ZMod.val_eq_zero z).mp h)
      · exact Or.inr ((ZMod.val_injective 2) (by simpa only [ZMod.val_one_eq_one_mod] using h))
    rcases bits a with rfl | rfl <;> rcases bits b with rfl | rfl <;>
      simp [CharTwo.add_self_eq_zero]
  exact hb _ _

private lemma count_zero {d : ℕ} (z : Fin d → ZMod 2) :
    (∑ i, if z i = 0 then (1:ℝ) else 0) = (d:ℝ) - (hammingNorm z : ℝ) := by
  classical
  have h (i : Fin d) : (if z i = 0 then (1:ℝ) else 0) =
      1 - (if z i ≠ 0 then (1:ℝ) else 0) := by split_ifs <;> simp_all
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  rw [hammingNorm, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

private lemma pac_gram {d k T : ℕ} {ε : ℝ} (hd : 10 ≤ d) (hε : 0 < ε) (hε' : ε < 1/20)
    (M : Matrix (Fin d) (Fin k) (ZMod 2)) (x y : Fin k → ZMod 2) :
    inner ℂ (tensorPow T (exampleState (pacHardConcept M x) (pacHardDist d ε)))
      (tensorPow T (exampleState (pacHardConcept M y) (pacHardDist d ε))) =
      ((xorConvMatrix fun z => weightPowFun d (20*ε) T (M.mulVec z)) x y : ℂ) := by
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hD : ∀ i, 0 ≤ pacHardDist d ε i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 ≤ 1-20*ε
      linarith
    · change 0 ≤ 20*ε/(d:ℝ)
      positivity
  rw [tensor_inner, example_inner _ _ _ hD]
  simp only [xorConvMatrix, Matrix.of_apply, weightPowFun]
  rw [Complex.ofReal_pow]
  congr 2
  rw [Fin.sum_univ_succ]
  simp only [pacHardConcept, pacHardDist, Fin.cons_zero, Fin.cons_succ, ite_true]
  simp_rw [bit_eq]
  have h (i : Fin d) : (if (M.mulVec (x+y)) i = 0 then 20*ε/(d:ℝ) else 0) =
      (20*ε/(d:ℝ))*(if (M.mulVec (x+y)) i = 0 then 1 else 0) := by split_ifs <;> ring
  simp_rw [h]
  rw [← Finset.mul_sum, count_zero]
  field_simp
  ring

theorem solution {d k T : ℕ} {ε : ℝ} (hd : 10 ≤ d) (hε : 0 < ε) (hε' : ε < 1/20)
    (M : Matrix (Fin d) (Fin k) (ZMod 2)) (hM : M.rank = k) (hkd : k ≤ d) (hdk : d ≤ 4*k)
    (_hdist : ∀ x y : Fin k → ZMod 2, x ≠ y →
      (d:ℝ)/8 ≤ (hammingDist (M.mulVec x) (M.mulVec y) : ℝ))
    (hT : 1 ≤ T) (hTd : (T:ℝ) ≤ (d:ℝ)/(20*Real.exp 3*ε)) :
    pgmSuccess (fun _ : Fin k → ZMod 2 => ((2:ℝ)^k)⁻¹)
      (fun x => tensorPow T (exampleState (pacHardConcept M x) (pacHardDist d ε))) ≤
      4*Real.exp 1 / (2:ℝ)^((d:ℝ)/4+(T:ℝ)*ε) *
        Real.exp (8800*(T:ℝ)^2*ε^2/(d:ℝ)+4*Real.sqrt (5*(T:ℝ)*(d:ℝ)*ε)) := by
  classical
  let A := xorConvMatrix fun z => weightPowFun d (20*ε) T (M.mulVec z)
  let B := ((2:ℝ)^k)⁻¹ * (4*Real.exp 1*(1-(20*ε)/2)^T) *
    Real.exp (22*(T:ℝ)^2*(20*ε)^2/(d:ℝ)+2*Real.sqrt ((T:ℝ)*(d:ℝ)*(20*ε)))
  have hβ : 0 < 20*ε := by positivity
  have hβ1 : 20*ε ≤ 1 := by linarith
  have hTm : (T:ℝ) ≤ (d:ℝ)/(Real.exp 3*(20*ε)) := by
    convert hTd using 1; ring
  have hGram := QAlgorithms.pgmSuccess_uniform_real_gram
    (fun x => tensorPow T (exampleState (pacHardConcept M x) (pacHardDist d ε))) A
    (pac_gram hd hε hε' M)
  have hcard : (Fintype.card (Fin k → ZMod 2) : ℝ) = (2:ℝ)^k := by simp
  rw [hcard] at hGram
  have hsum : (∑ x : Fin k → ZMod 2, (psdSqrt A x x)^2) ≤ (2:ℝ)^k * B := by
    calc
      _ ≤ ∑ _x : Fin k → ZMod 2, B := by
        apply Finset.sum_le_sum
        intro x _
        exact diag_bound hd hβ hβ1 hT hTm hkd M hM x
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hpre : pgmSuccess (fun _ : Fin k → ZMod 2 => ((2:ℝ)^k)⁻¹)
      (fun x => tensorPow T (exampleState (pacHardConcept M x) (pacHardDist d ε))) ≤ B := by
    rw [hGram]
    calc
      _ ≤ ((2:ℝ)^k)⁻¹ * ((2:ℝ)^k * B) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by rw [inv_mul_cancel_left₀ (by positivity)]
  apply hpre.trans
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have ha : 0 ≤ 1-10*ε := by linarith
  have hp : (1-10*ε)^T ≤ (2:ℝ)^(-((T:ℝ)*ε)) := by
    calc
      _ ≤ (Real.exp (-10*ε))^T :=
        pow_le_pow_left₀ ha (by linarith [Real.add_one_le_exp (-10*ε)]) T
      _ = Real.exp (-(10*(T:ℝ)*ε)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (Real.log 2 * -((T:ℝ)*ε)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (by positivity : 0 ≤ (T:ℝ)*ε) (show 0 ≤ 10-Real.log 2 by linarith)]
      _ = _ := (Real.rpow_def_of_pos (by norm_num) _).symm
  have hk : (d:ℝ)/4 ≤ (k:ℝ) := by
    have hc : (d:ℝ) ≤ 4*(k:ℝ) := by exact_mod_cast hdk
    linarith
  have hden : (2:ℝ)^((d:ℝ)/4+(T:ℝ)*ε) ≤ (2:ℝ)^k * (2:ℝ)^((T:ℝ)*ε) := by
    rw [Real.rpow_add (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (Real.rpow_natCast _ _)
  have hbase : ((2:ℝ)^k)⁻¹ * (4*Real.exp 1*(1-(20*ε)/2)^T) ≤
      4*Real.exp 1 / (2:ℝ)^((d:ℝ)/4+(T:ℝ)*ε) := by
    calc
      _ ≤ ((2:ℝ)^k)⁻¹ * (4*Real.exp 1*(2:ℝ)^(-((T:ℝ)*ε))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show 1-(20*ε)/2 = 1-10*ε by ring]
        exact hp
      _ = 4*Real.exp 1 / ((2:ℝ)^k * (2:ℝ)^((T:ℝ)*ε)) := by
        rw [Real.rpow_neg (by norm_num)]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hsqrt : 2*Real.sqrt ((T:ℝ)*(d:ℝ)*(20*ε)) = 4*Real.sqrt (5*(T:ℝ)*(d:ℝ)*ε) := by
    have he : (T:ℝ)*(d:ℝ)*(20*ε) = 4*(5*(T:ℝ)*(d:ℝ)*ε) := by ring
    rw [he, Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
    ring
  dsimp [B]
  apply mul_le_mul hbase _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  rw [hsqrt]
  ring_nf
  exact le_rfl
