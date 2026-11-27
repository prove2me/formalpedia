-- Prove2me | solution 1 for ParityDegreeDepth.Main.fact_B_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:02:59.133554+00:00
-- url     : https://prove2.me/submissions/21de029c-44d6-4f4b-8458-42a79c0ff746

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section
namespace ParityDegreeDepth.Main

private abbrev Vec (n : ℕ) (F : Type) := Fin n → F

private def multiplicity {F : Type} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (a : Vec n F) : ℕ∞ :=
  ⨅ e ∈ (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) P).support,
    (KakeyaHasse.order e : ℕ∞)

end ParityDegreeDepth.Main

section P2MHasseSec
open MvPolynomial
namespace P2MHasse
variable {σ F : Type} [Fintype σ] [Field F]

lemma coeff_hasse (i : σ →₀ ℕ) (P : MvPolynomial σ F) (b : σ →₀ ℕ) :
    (KakeyaHasse.hasse i P).coeff b = KakeyaHasse.multiChoose (b + i) i * P.coeff (b + i) := by
  classical
  unfold KakeyaHasse.hasse
  simp [MvPolynomial.coeff]

lemma multiChoose_zero (b : σ →₀ ℕ) : (KakeyaHasse.multiChoose b 0 : F) = 1 := by
  simp [KakeyaHasse.multiChoose]

lemma hasse_add (c : σ →₀ ℕ) (p q : MvPolynomial σ F) :
    KakeyaHasse.hasse c (p + q) = KakeyaHasse.hasse c p + KakeyaHasse.hasse c q := by
  ext b; simp only [coeff_hasse, coeff_add, mul_add]

lemma hasse_C (c : σ →₀ ℕ) (r : F) :
    KakeyaHasse.hasse c (C r) = if c = 0 then C r else 0 := by
  classical
  ext b
  rw [coeff_hasse, coeff_C]
  split_ifs with h1 h2 h2
  · rw [h2] at h1 ⊢; simp only [add_zero] at h1; subst h1; simp [multiChoose_zero]
  · exact absurd (add_eq_zero.mp h1.symm).2 h2
  · subst h2; simp only [add_zero] at h1; simp [coeff_C, h1]
  · simp

variable [DecidableEq σ]

lemma choose_id (x y : ℕ) :
    (x + y).choose y * (if x + y = 0 then 0 else 1) =
      (if x = 0 then 0 else (x + y - 1).choose y) +
        (if y = 0 then 0 else (x + y - 1).choose (y - 1)) := by
  rcases Nat.eq_zero_or_pos x with hx | hx <;> rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hx; subst hy; simp
  · subst hx; simp [hy.ne']
  · subst hy; simp [hx.ne']
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), mul_one]
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    rw [show x + (y' + 1) = (x + y' - 1 + 1) + 1 by omega, Nat.choose_succ_succ]
    rw [show x + y' - 1 + 1 + 1 - 1 = x + y' - 1 + 1 by omega, show y' + 1 - 1 = y' by omega]
    ring

lemma prod_split (i : σ) (f : σ → F) : ∏ j, f j = f i * ∏ j ∈ Finset.univ.erase i, f j :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

lemma hasse_mul_X (c : σ →₀ ℕ) (p : MvPolynomial σ F) (i : σ) :
    KakeyaHasse.hasse c (p * X i) = KakeyaHasse.hasse c p * X i +
      (if c i = 0 then 0 else KakeyaHasse.hasse (c - Finsupp.single i 1) p) := by
  classical
  ext b
  rw [coeff_add, coeff_hasse, coeff_mul_X', coeff_mul_X']
  set δ := Finsupp.single i 1 with hδ
  have hδi : δ i = 1 := by simp [hδ]
  have hδj : ∀ j, j ≠ i → δ j = 0 := fun j hj => by simp [hδ, Finsupp.single_apply, Ne.symm hj]
  have hX : ∀ q : MvPolynomial σ F, q.coeff (b + c - δ) = q.coeff (b + c - δ) := fun _ => rfl
  -- normalize everything to coefficient of p at b + c - δ
  have e1 : b i ≠ 0 → b - δ + c = b + c - δ := by
    intro h; ext j; simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hj : j = i
    · subst hj; rw [hδi]; omega
    · rw [hδj j hj]; omega
  have e2 : c i ≠ 0 → b + (c - δ) = b + c - δ := by
    intro h; ext j; simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hj : j = i
    · subst hj; rw [hδi]; omega
    · rw [hδj j hj]; omega
  simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply]
  set R : F := ∏ j ∈ Finset.univ.erase i, (((b + c) j).choose (c j) : F) with hR
  have hmc : ∀ u v : σ →₀ ℕ, (∀ j, j ≠ i → u j = b j + c j ∧ v j = c j) →
      (KakeyaHasse.multiChoose u v : F) = ((u i).choose (v i) : F) * R := by
    intro u v h
    unfold KakeyaHasse.multiChoose
    rw [prod_split i]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    obtain ⟨h1, h2⟩ := h j (Finset.ne_of_mem_erase hj)
    rw [h1, h2]; simp
  have hA := hmc (b + c) c (fun j _ => ⟨by simp, rfl⟩)
  have key := choose_id (b i) (c i)
  by_cases hb : b i = 0 <;> by_cases hc : c i = 0
  · simp [hb, hc]
  · have hB := hmc (b + c - δ) (c - δ) (fun j hj => ⟨by simp [hδj j hj], by simp [hδj j hj]⟩)
    simp only [hb, hc, zero_add, ne_eq, not_false_eq_true, if_true, if_false, ite_not]
    rw [coeff_hasse, e2 hc, hA, hB]
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, hδi, hb, zero_add,
      Nat.choose_self, Nat.cast_one]
  · have hB := hmc (b + c - δ) c (fun j hj => ⟨by simp [hδj j hj], rfl⟩)
    simp only [hb, hc, add_zero, ne_eq, not_false_eq_true, if_true, if_false]
    rw [coeff_hasse, e1 hb, hA, hB, coeff_zero, add_zero]
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, hδi, hc, add_zero,
      Nat.choose_zero_right, Nat.cast_one]
  · have hB := hmc (b + c - δ) c (fun j hj => ⟨by simp [hδj j hj], rfl⟩)
    have hC := hmc (b + c - δ) (c - δ) (fun j hj => ⟨by simp [hδj j hj], by simp [hδj j hj]⟩)
    rw [if_pos (by omega), if_pos hb, if_neg hc, coeff_hasse, coeff_hasse, e1 hb, e2 hc, hA, hB, hC]
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, hδi]
    rw [if_neg (by omega), if_neg hb, if_neg hc, mul_one] at key
    have key' : ((b i + c i).choose (c i) : F) =
        ((b i + c i - 1).choose (c i) : F) + ((b i + c i - 1).choose (c i - 1) : F) := by
      rw [key, Nat.cast_add]
    rw [key']; ring

lemma taylor (a : σ → F) (P : MvPolynomial σ F) : ∀ c : σ →₀ ℕ,
    (aeval (fun i => X i + C (a i)) P).coeff c = eval a (KakeyaHasse.hasse c P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r =>
    intro c
    rw [aeval_C, hasse_C, MvPolynomial.algebraMap_eq, coeff_C]
    by_cases h : c = 0
    · subst h; simp
    · simp [h, Ne.symm h]
  | add p q hp hq =>
    intro c
    rw [map_add, coeff_add, hp, hq, hasse_add, map_add]
  | mul_X p i hp =>
    intro c
    rw [map_mul, aeval_X, mul_add, coeff_add, coeff_mul_X', mul_comm _ (C (a i)), coeff_C_mul, hasse_mul_X, map_add,
      map_mul, eval_X, hp]
    by_cases h : c i = 0
    · simp only [Finsupp.mem_support_iff, ne_eq, h, not_true_eq_false, if_false, if_true, hp, map_zero]
      ring
    · simp only [Finsupp.mem_support_iff, ne_eq, h, not_false_eq_true, if_true, if_false, hp]
      ring

lemma hasse_hasse (b e : σ →₀ ℕ) (P : MvPolynomial σ F) :
    KakeyaHasse.hasse b (KakeyaHasse.hasse e P) =
      C (KakeyaHasse.multiChoose (b + e) e) * KakeyaHasse.hasse (b + e) P := by
  ext x
  rw [coeff_hasse, coeff_hasse, coeff_C_mul, coeff_hasse]
  simp only [add_assoc]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  unfold KakeyaHasse.multiChoose
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  congr 1
  have := Nat.choose_mul (n := x j + (b j + e j)) (k := b j + e j) (s := e j) (by omega)
  rw [mul_comm ((b j + e j).choose (e j)), this,
    show x j + (b j + e j) - e j = x j + b j by omega, show b j + e j - e j = b j by omega]
  ring

lemma order_add (b e : σ →₀ ℕ) :
    KakeyaHasse.order (b + e) = KakeyaHasse.order b + KakeyaHasse.order e := by
  unfold KakeyaHasse.order
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

noncomputable def mult (P : MvPolynomial σ F) (a : σ → F) : ℕ∞ :=
  ⨅ e ∈ (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i)) P).support,
    (KakeyaHasse.order e : ℕ∞)

theorem part1 (P : MvPolynomial σ F) (e : σ →₀ ℕ) (a : σ → F) :
    mult P a - (KakeyaHasse.order e : ℕ∞) ≤ mult (KakeyaHasse.hasse e P) a := by
  unfold mult
  refine le_iInf₂ fun b hb => ?_
  rw [mem_support_iff, taylor, hasse_hasse, eval_mul, eval_C] at hb
  have hb' : b + e ∈ (aeval (fun i => X i + C (a i)) P).support := by
    rw [mem_support_iff, taylor]; exact right_ne_zero_of_mul hb
  have := iInf₂_le (f := fun c (_ : c ∈ (aeval (fun i => X i + C (a i)) P).support) =>
    (KakeyaHasse.order c : ℕ∞)) (b + e) hb'
  rw [order_add, Nat.cast_add] at this
  exact tsub_le_iff_right.mpr this

theorem part2 (P : MvPolynomial σ F) (a v : σ → F)
    (hne : KakeyaPolynomialMethods.lineMap a v P ≠ 0) :
    mult P a ≤ ((KakeyaPolynomialMethods.lineMap a v P).rootMultiplicity 0 : ℕ∞) := by
  classical
  set Q := aeval (fun i => X i + C (a i)) P with hQ
  have hline : KakeyaPolynomialMethods.lineMap a v P =
      aeval (fun j => Polynomial.X * Polynomial.C (v j)) Q := by
    have : (KakeyaPolynomialMethods.lineMap a v : MvPolynomial σ F →ₐ[F] Polynomial F) =
        (aeval (fun j => Polynomial.X * Polynomial.C (v j))).comp
          (aeval (fun i => X i + C (a i))) := by
      apply MvPolynomial.algHom_ext; intro j
      simp [KakeyaPolynomialMethods.lineMap]; ring
    rw [this]; rfl
  have hQ0 : Q ≠ 0 := by
    intro h; apply hne; rw [hline, h, map_zero]
  have hsupp : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hQ0
  obtain ⟨c0, hc0, hmin⟩ := Q.support.exists_mem_eq_inf' hsupp (fun c => KakeyaHasse.order c)
  have hdiv : Polynomial.X ^ KakeyaHasse.order c0 ∣ KakeyaPolynomialMethods.lineMap a v P := by
    rw [hline, Q.as_sum, map_sum]
    refine Finset.dvd_sum fun c hc => ?_
    rw [aeval_monomial]
    apply dvd_mul_of_dvd_right
    have hle : KakeyaHasse.order c0 ≤ KakeyaHasse.order c := by
      rw [← hmin]; exact Finset.inf'_le _ hc
    refine (pow_dvd_pow _ hle).trans ?_
    unfold Finsupp.prod KakeyaHasse.order Finsupp.sum
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact dvd_mul_right _ _
  have hroot : KakeyaHasse.order c0 ≤ (KakeyaPolynomialMethods.lineMap a v P).rootMultiplicity 0 := by
    rw [Polynomial.le_rootMultiplicity_iff hne, map_zero, sub_zero]; exact hdiv
  calc mult P a ≤ (KakeyaHasse.order c0 : ℕ∞) := by
        unfold mult
        exact iInf₂_le (f := fun c (_ : c ∈ Q.support) => (KakeyaHasse.order c : ℕ∞)) c0 hc0
    _ ≤ _ := by exact_mod_cast hroot

end P2MHasse
end P2MHasseSec

open ParityDegreeDepth.Main in
/-- fact B 2; Zhang, STOC 2027 submission #798. -/
theorem solution {F : Type} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (e : Fin n →₀ ℕ) (a : Vec n F) :
    ParityDegreeDepth.Main.multiplicity P a - (KakeyaHasse.order e : ℕ∞) ≤
      ParityDegreeDepth.Main.multiplicity (KakeyaHasse.hasse e P) a ∧
    (∀ (v : Vec n F), v ≠ 0 → KakeyaPolynomialMethods.lineMap a v P ≠ 0 →
      ParityDegreeDepth.Main.multiplicity P a ≤
        ((KakeyaPolynomialMethods.lineMap a v P).rootMultiplicity 0 : ℕ∞)) :=
  ⟨P2MHasse.part1 P e a, fun v _ h => P2MHasse.part2 P a v h⟩
