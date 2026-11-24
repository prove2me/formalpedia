-- Prove2me | solution 1 for SparseTensorInj.Certify.lemma_48
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T22:44:39.727929+00:00
-- url     : https://prove2.me/submissions/afe08b52-e4b9-474c-824f-5a3b385757c1

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_OddCertificate

open Matrix

namespace SparseTensorInj.Certify


theorem sum_inj_tuples {k n : ℕ} (F : (Fin k → Fin n) → ℝ)
    (hF : ∀ (π : Equiv.Perm (Fin k)) (i : Fin k → Fin n), F (i ∘ π) = F i) :
    ∑ i : Fin k → Fin n, (if (Finset.univ.image i).card = k then F i else 0) =
      (Nat.factorial k : ℝ) * ∑ e : KSubset n k, F (fun m => e.1.orderEmbOfFin e.2 m) := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (Finset.univ.filter (fun i : Fin k → Fin n => (Finset.univ.image i).card = k))
    (p := fun i : Fin k → Fin n => (Finset.univ.image i).card = k) (by intro i; simp) F]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset {i : Fin k → Fin n // (Finset.univ.image i).card = k})
    (fun i => (⟨Finset.univ.image i.1, i.2⟩ : KSubset n k))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have key : ∀ i : {i : Fin k → Fin n // (Finset.univ.image i).card = k},
      (⟨Finset.univ.image i.1, i.2⟩ : KSubset n k) = e → ∃ π : Equiv.Perm (Fin k),
        i.1 = fun m => e.1.orderEmbOfFin e.2 (π m) := by
    intro i hi
    have hi' : Finset.univ.image i.1 = e.1 := congrArg Subtype.val hi
    have hmem : ∀ m, i.1 m ∈ e.1 := by
      intro m; rw [← hi']; simp
    have hinj : Function.Injective i.1 := by
      have := (Finset.card_image_iff (s := (Finset.univ : Finset (Fin k))) (f := i.1)).mp (by rw [Finset.card_univ, Fintype.card_fin]; exact i.2)
      intro a b h; exact this (by simp) (by simp) h
    let σ : Fin k → Fin k := fun m => (e.1.orderIsoOfFin e.2).symm ⟨i.1 m, hmem m⟩
    have hσ : Function.Injective σ := by
      intro a b h
      have := (e.1.orderIsoOfFin e.2).symm.injective h
      exact hinj (congrArg Subtype.val this)
    refine ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσ), ?_⟩
    funext m
    simp only [Equiv.ofBijective_apply, σ]
    rw [← Finset.coe_orderIsoOfFin_apply]
    have := (e.1.orderIsoOfFin e.2).apply_symm_apply ⟨i.1 m, hmem m⟩
    exact (congrArg Subtype.val this).symm
  have hval : ∀ i : {i : Fin k → Fin n // (Finset.univ.image i).card = k},
      (⟨Finset.univ.image i.1, i.2⟩ : KSubset n k) = e → F i.1 = F (fun m => e.1.orderEmbOfFin e.2 m) := by
    intro i hi
    obtain ⟨π, hπ⟩ := key i hi
    rw [hπ]
    exact hF π (fun m => e.1.orderEmbOfFin e.2 m)
  rw [Finset.sum_congr rfl (fun i hi => hval i (Finset.mem_filter.mp hi).2), Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hc : (Finset.univ.filter (fun i : {i : Fin k → Fin n // (Finset.univ.image i).card = k} =>
      (⟨Finset.univ.image i.1, i.2⟩ : KSubset n k) = e)).card = (Finset.univ : Finset (Equiv.Perm (Fin k))).card := by
    refine Finset.card_bij (fun i hi => (key i (Finset.mem_filter.mp hi).2).choose) ?_ ?_ ?_
    · intro i hi; simp
    · intro a ha b hb h
      apply Subtype.ext
      rw [(key a (Finset.mem_filter.mp ha).2).choose_spec, (key b (Finset.mem_filter.mp hb).2).choose_spec, h]
    · intro π _
      have hinj : Function.Injective (fun m => e.1.orderEmbOfFin e.2 (π m)) := by
        intro a b h; exact π.injective ((e.1.orderEmbOfFin e.2).injective h)
      have himg : Finset.univ.image (fun m => e.1.orderEmbOfFin e.2 (π m)) = e.1 := by
        ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨m, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
        · intro hx
          have := Finset.range_orderEmbOfFin e.1 e.2
          have hx' : x ∈ Set.range (e.1.orderEmbOfFin e.2) := by rw [this]; exact hx
          obtain ⟨m, hm⟩ := hx'
          exact ⟨π.symm m, by simpa using hm⟩
      have hc : (Finset.univ.image (fun m => e.1.orderEmbOfFin e.2 (π m))).card = k := by
        rw [himg]; exact e.2
      refine ⟨⟨fun m => e.1.orderEmbOfFin e.2 (π m), hc⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Subtype.ext himg
      · have h2 := (key ⟨fun m => e.1.orderEmbOfFin e.2 (π m), hc⟩ (Subtype.ext himg)).choose_spec
        ext m
        have := congrFun h2 m
        exact congrArg Fin.val ((e.1.orderEmbOfFin e.2).injective this).symm
  rw [hc]; simp [Fintype.card_perm]



theorem prod_sum_sq {k n : ℕ} (x : Fin n → ℝ) :
    ∑ i : Fin k → Fin n, ∏ j : Fin k, x (i j) ^ 2 = (∑ i, x i ^ 2) ^ k := by
  have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin n))) (fun _ i => x i ^ 2)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  rw [Fintype.piFinset_univ] at this
  simpa using this.symm

theorem frob_bound {k n : ℕ} (S : Tensor k n) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    |multilinearForm S x| ≤ frobNorm S := by
  unfold multilinearForm frobNorm
  have h1 : (∑ i : Fin k → Fin n, S i * ∏ j, x (i j)) ^ 2 ≤
      (∑ i : Fin k → Fin n, S i ^ 2) * ∑ i : Fin k → Fin n, (∏ j, x (i j)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 : ∑ i : Fin k → Fin n, (∏ j, x (i j)) ^ 2 = 1 := by
    have := prod_sum_sq (k := k) x
    rw [hx, one_pow] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.prod_pow])
  rw [h2, mul_one] at h1
  exact Real.abs_le_sqrt h1

theorem tensor_decomp {k n : ℕ} (T : Tensor k n) (x : Fin n → ℝ) :
    multilinearForm T x = multilinearForm (zeroRepeated T) x + multilinearForm (T - zeroRepeated T) x := by
  unfold multilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.sub_apply]; ring

theorem multilinear_zeroRepeated {q n : ℕ} (T : Tensor (2 * q + 1) n) (hT : IsSymmetric T) (x : Fin n → ℝ) :
    multilinearForm (zeroRepeated T) x =
      (Nat.factorial (2 * q + 1) : ℝ) * ∑ e : KSubset n (2 * q + 1), coef T e * ∏ m, x (sortedElt e m) := by
  have := sum_inj_tuples (k := 2 * q + 1) (n := n) (fun i => T i * ∏ j, x (i j)) (by
    intro π i
    simp only [Function.comp]
    rw [hT π i]
    congr 1
    exact Fintype.prod_equiv π _ _ (fun _ => rfl))
  unfold multilinearForm zeroRepeated
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) (this.trans rfl)
  split_ifs <;> simp

theorem sum_sq_sorted {k n : ℕ} (g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i) :
    (Nat.factorial k : ℝ) * ∑ e : KSubset n k, ∏ m, g (e.1.orderEmbOfFin e.2 m) ≤ (∑ i, g i) ^ k := by
  have h := sum_inj_tuples (k := k) (n := n) (fun i => ∏ j, g (i j)) (by
    intro π i
    exact Fintype.prod_equiv π _ _ (fun _ => rfl))
  rw [← h]
  have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin n))) (fun _ i => g i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  rw [Fintype.piFinset_univ] at this
  rw [this]
  refine Finset.sum_le_sum (fun i _ => ?_)
  split_ifs
  · exact le_rfl
  · exact Finset.prod_nonneg (fun j _ => hg _)



noncomputable def zvec {n q : ℕ} (x : Fin n → ℝ) (J : QSet n q) : ℝ := ∏ j ∈ J.1, x j

theorem prod_split {n q : ℕ} (x : Fin n → ℝ) (e : KSubset n (2 * q + 1)) :
    ∏ m, x (sortedElt e m) = x (minElt e) * zvec x (Jset e) * zvec x (Kset e) := by
  unfold zvec Jset Kset
  rw [Finset.prod_map, Finset.prod_map]
  simp only [Function.Embedding.trans_apply]
  rw [Fin.prod_univ_succ]
  have : ∏ i : Fin (2 * q), x (sortedElt e i.succ) =
      (∏ i : Fin q, x (sortedElt e (posJ q i))) * ∏ i : Fin q, x (sortedElt e (posK q i)) := by
    rw [← Fintype.prod_equiv (finCongr (two_mul q).symm) (fun i : Fin (q + q) => x (sortedElt e (Fin.succ (Fin.cast (two_mul q).symm i))))
      (fun i : Fin (2 * q) => x (sortedElt e i.succ)) (by intro i; simp)]
    rw [Fin.prod_univ_add]
    congr 1
    all_goals
      refine Finset.prod_congr rfl (fun i _ => ?_)
      congr 2
      ext
      first
        | (show _ = q + 1 + i.val; simp; omega)
        | (show _ = i.val + 1; simp)
  rw [this]
  simp only [minElt, Fin.zero_eta]
  rw [← mul_assoc]
  rfl

theorem quad_P {n q : ℕ} (z : QSet n q → ℝ) (e : KSubset n (2 * q + 1)) :
    ∑ a, ∑ b, z a * Pmat e a b * z b = 2 * z (Jset e) * z (Kset e) := by
  classical
  unfold Pmat
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  ring

theorem quad_slice {n q : ℕ} (T : Tensor (2 * q + 1) n) (z : QSet n q → ℝ) (i : Fin n) :
    ∑ a, ∑ b, z a * slice T i a b * z b =
      ∑ e ∈ Finset.univ.filter (fun e : KSubset n (2 * q + 1) => minElt e = i),
        coef T e * (2 * z (Jset e) * z (Kset e)) := by
  unfold slice
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have h : ∀ a b, z a * (∑ e ∈ Finset.univ.filter (fun e : KSubset n (2 * q + 1) => minElt e = i),
      coef T e * Pmat e a b) * z b = ∑ e ∈ Finset.univ.filter (fun e : KSubset n (2 * q + 1) => minElt e = i),
      coef T e * (z a * Pmat e a b * z b) := by
    intro a b
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  simp only [h]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← quad_P z e, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]

theorem sumS_eq {n q : ℕ} (T : Tensor (2 * q + 1) n) (x : Fin n → ℝ) :
    ∑ e : KSubset n (2 * q + 1), coef T e * ∏ m, x (sortedElt e m) =
      (1 / 2) * ∑ i, x i * ∑ a, ∑ b, zvec x a * slice T i a b * zvec x b := by
  simp only [quad_slice]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (KSubset n (2 * q + 1))) (fun e => minElt e)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_congr rfl (fun e he => by rw [prod_split x e, (Finset.mem_filter.mp he).2])]
  refine Finset.sum_congr rfl (fun e he => ?_)
  ring



theorem opNorm_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (w : ι → ℝ) :
    ∑ p, ∑ r, w p * A p r * w r ≤ opNorm A * ∑ p, w p ^ 2 := by
  unfold opNorm
  set L := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) with hL
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 w
  have h1 : L v = WithLp.toLp 2 (A.mulVec w) := by
    simp [hL, v, Matrix.toEuclideanLin_toLp]
  have h2 : ∑ p, ∑ r, w p * A p r * w r = inner ℝ v (L v) := by
    rw [h1]
    simp only [PiLp.inner_apply, v, Matrix.mulVec, dotProduct]
    simp only [RCLike.inner_apply, conj_trivial, WithLp.ofLp_toLp]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  have h3 : ∑ p, w p ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    simp [v]
  rw [h2, h3]
  calc inner ℝ v (L v) ≤ ‖v‖ * ‖L v‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖L‖ * ‖v‖) := by gcongr; exact L.le_opNorm v
    _ = ‖L‖ * ‖v‖ ^ 2 := by ring

theorem quad_kron {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (z : ι → ℝ) :
    ∑ p : ι × ι, ∑ r : ι × ι, (z p.1 * z p.2) * (kronecker A A) p r * (z r.1 * z r.2) =
      (∑ a, ∑ c, z a * A a c * z c) ^ 2 := by
  rw [sq]
  simp only [Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring



theorem zsq_le {n q : ℕ} (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    (Nat.factorial q : ℝ) * ∑ J : QSet n q, zvec x J ^ 2 ≤ 1 := by
  have h := sum_sq_sorted (k := q) (fun i => x i ^ 2) (fun i => sq_nonneg _)
  rw [hx, one_pow] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine Finset.sum_congr rfl (fun J _ => ?_)
  unfold zvec
  rw [← Finset.prod_pow]
  have := Finset.map_orderEmbOfFin_univ J.1 J.2
  conv_lhs => rw [← this]
  rw [Finset.prod_map]
  rfl

theorem Jset_ne_Kset {n q : ℕ} (hq : 1 ≤ q) (e : KSubset n (2 * q + 1)) : Jset e ≠ Kset e := by
  intro h
  have h1 : (sortedElt e) (posJ q ⟨0, hq⟩) ∈ (Jset e).1 := by
    simp [Jset]
  rw [h] at h1
  simp only [Kset, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply] at h1
  obtain ⟨j, hj⟩ := h1
  have := (sortedElt e).injective hj
  have h2 : (posK q j).val = (posJ q ⟨0, hq⟩).val := congrArg Fin.val this
  change q + 1 + j.val = 0 + 1 at h2
  omega

theorem dmax_nonneg {n q : ℕ} (T : Tensor (2 * q + 1) n) : 0 ≤ dmax T := by
  unfold dmax
  refine Real.iSup_nonneg (fun J => Real.iSup_nonneg (fun K => ?_))
  exact Finset.sum_nonneg (fun e _ => sq_nonneg _)

theorem dJK_le {n q : ℕ} (T : Tensor (2 * q + 1) n) (J K : QSet n q) : dJK T J K ≤ dmax T := by
  unfold dmax
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove J)
  exact le_ciSup (f := fun K => dJK T J K) (Set.finite_range _).bddAbove K

theorem dpart {n q : ℕ} (hq : 1 ≤ q) (T : Tensor (2 * q + 1) n) (z : QSet n q → ℝ) :
    ∑ e : KSubset n (2 * q + 1), coef T e ^ 2 * (2 * z (Jset e) * z (Kset e)) ^ 2 ≤
      2 * dmax T * (∑ J, z J ^ 2) ^ 2 := by
  classical
  have h1 : ∑ J : QSet n q, ∑ K : QSet n q, dJK T J K * (z J ^ 2 * z K ^ 2) =
      2 * ∑ e : KSubset n (2 * q + 1), coef T e ^ 2 * (z (Jset e) ^ 2 * z (Kset e) ^ 2) := by
    unfold dJK
    simp only [Finset.sum_mul, Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun J _ => Finset.sum_comm)]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have hne := Jset_ne_Kset hq e
    have : ∀ J K : QSet n q, (if (Jset e = J ∧ Kset e = K) ∨ (Jset e = K ∧ Kset e = J) then
        coef T e ^ 2 * (z J ^ 2 * z K ^ 2) else 0) =
        (if Jset e = J ∧ Kset e = K then coef T e ^ 2 * (z J ^ 2 * z K ^ 2) else 0) +
        (if Jset e = K ∧ Kset e = J then coef T e ^ 2 * (z J ^ 2 * z K ^ 2) else 0) := by
      intro J K
      by_cases hA : Jset e = J ∧ Kset e = K
      · have hB : ¬ (Jset e = K ∧ Kset e = J) := by
          rintro ⟨a, b⟩; exact hne (hA.1.trans (b.symm ▸ rfl))
        rw [if_pos (Or.inl hA), if_pos hA, if_neg hB, add_zero]
      · by_cases hB : Jset e = K ∧ Kset e = J
        · rw [if_pos (Or.inr hB), if_neg hA, if_pos hB, zero_add]
        · rw [if_neg (by tauto), if_neg hA, if_neg hB, add_zero]
    simp only [ite_mul, zero_mul, this, Finset.sum_add_distrib]
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have h2 : ∑ J : QSet n q, ∑ K : QSet n q, dJK T J K * (z J ^ 2 * z K ^ 2) ≤
      dmax T * (∑ J, z J ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun J _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun K _ => ?_)
    have := dJK_le T J K
    nlinarith [mul_nonneg (sq_nonneg (z J)) (sq_nonneg (z K)), dmax_nonneg T]
  have h3 : ∑ e : KSubset n (2 * q + 1), coef T e ^ 2 * (2 * z (Jset e) * z (Kset e)) ^ 2 =
      4 * ∑ e : KSubset n (2 * q + 1), coef T e ^ 2 * (z (Jset e) ^ 2 * z (Kset e) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  rw [h3]
  linarith


theorem dq_D {n q : ℕ} (T : Tensor (2 * q + 1) n) (z : QSet n q → ℝ) :
    ∑ p : QSet n q × QSet n q, ∑ r : QSet n q × QSet n q, (z p.1 * z p.2) * Dmat T p r * (z r.1 * z r.2) =
      ∑ e : KSubset n (2 * q + 1), coef T e ^ 2 * (2 * z (Jset e) * z (Kset e)) ^ 2 := by
  unfold Dmat
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have h : ∀ p r : QSet n q × QSet n q, (z p.1 * z p.2) * (∑ e : KSubset n (2 * q + 1),
      coef T e ^ 2 * (kronecker (Pmat e) (Pmat e)) p r) * (z r.1 * z r.2) =
      ∑ e : KSubset n (2 * q + 1), coef T e ^ 2 *
        ((z p.1 * z p.2) * (kronecker (Pmat e) (Pmat e)) p r * (z r.1 * z r.2)) := by
    intro p r
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  simp only [h]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [← Finset.mul_sum]
  rw [quad_kron, quad_P]

theorem dq_Mt {n q : ℕ} (T : Tensor (2 * q + 1) n) (z : QSet n q → ℝ) :
    ∑ p : QSet n q × QSet n q, ∑ r : QSet n q × QSet n q, (z p.1 * z p.2) *
      (∑ i : Fin n, kronecker (slice T i) (slice T i)) p r * (z r.1 * z r.2) =
      ∑ i : Fin n, (∑ a, ∑ b, z a * slice T i a b * z b) ^ 2 := by
  simp only [Matrix.sum_apply]
  have h : ∀ p r : QSet n q × QSet n q, (z p.1 * z p.2) * (∑ i : Fin n, (kronecker (slice T i) (slice T i)) p r)
      * (z r.1 * z r.2) = ∑ i : Fin n, ((z p.1 * z p.2) * (kronecker (slice T i) (slice T i)) p r * (z r.1 * z r.2)) := by
    intro p r
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [h]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => quad_kron (slice T i) z)



theorem sum_w_sq {ι : Type*} [Fintype ι] (z : ι → ℝ) :
    ∑ p : ι × ι, (z p.1 * z p.2) ^ 2 = (∑ a, z a ^ 2) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

theorem key_bound {q n : ℕ} (hq : 1 ≤ q) (T : Tensor (2 * q + 1) n) (hT : IsSymmetric T)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    |multilinearForm (zeroRepeated T) x| ≤
      ((Nat.factorial (2 * q + 1) : ℝ) / (2 * (Nat.factorial q : ℝ))) *
        Real.sqrt (opNorm (oddM T) + 2 * dmax T) := by
  set f : ℝ := (Nat.factorial q : ℝ) with hf
  have hfpos : 0 < f := by rw [hf]; exact_mod_cast Nat.factorial_pos q
  set z : QSet n q → ℝ := zvec x with hz
  set Z : ℝ := ∑ J, z J ^ 2 with hZ
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hfZ : f * Z ≤ 1 := zsq_le x hx
  set S : ℝ := ∑ e : KSubset n (2 * q + 1), coef T e * ∏ m, x (sortedElt e m) with hS
  have hS1 : multilinearForm (zeroRepeated T) x = (Nat.factorial (2 * q + 1) : ℝ) * S :=
    multilinear_zeroRepeated T hT x
  have hS2 : S = (1 / 2) * ∑ i, x i * ∑ a, ∑ b, z a * slice T i a b * z b := sumS_eq T x
  have hCS : (∑ i, x i * ∑ a, ∑ b, z a * slice T i a b * z b) ^ 2 ≤
      ∑ i, (∑ a, ∑ b, z a * slice T i a b * z b) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun i => ∑ a, ∑ b, z a * slice T i a b * z b)
    rwa [hx, one_mul] at this
  set w : QSet n q × QSet n q → ℝ := fun p => z p.1 * z p.2 with hw
  have hMt := dq_Mt T z
  have hsplit : ∑ p : QSet n q × QSet n q, ∑ r : QSet n q × QSet n q, w p *
      (∑ i : Fin n, kronecker (slice T i) (slice T i)) p r * w r =
      ∑ p : QSet n q × QSet n q, ∑ r : QSet n q × QSet n q, w p * oddM T p r * w r +
      ∑ p : QSet n q × QSet n q, ∑ r : QSet n q × QSet n q, w p * Dmat T p r * w r := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [oddM, Matrix.sub_apply]
    ring
  have hM := opNorm_quad (oddM T) w
  have hw2 : ∑ p, w p ^ 2 = Z ^ 2 := sum_w_sq z
  have hD := dpart hq T z
  have hDq := dq_D T z
  have hQ : ∑ i, (∑ a, ∑ b, z a * slice T i a b * z b) ^ 2 ≤ (opNorm (oddM T) + 2 * dmax T) * Z ^ 2 := by
    rw [← hMt]
    rw [hsplit]
    have : ∑ p : QSet n q × QSet n q, ∑ r : QSet n q × QSet n q, w p * Dmat T p r * w r ≤ 2 * dmax T * Z ^ 2 := by
      rw [hw]; simp only []; rw [hDq]; exact hD
    rw [hw2] at hM
    nlinarith
  have hM0 : 0 ≤ opNorm (oddM T) := norm_nonneg _
  have hR0 : 0 ≤ opNorm (oddM T) + 2 * dmax T := by linarith [dmax_nonneg T]
  have hfZ2 : (f * Z) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hfZ
  have hfin : (2 * f * S) ^ 2 ≤ opNorm (oddM T) + 2 * dmax T := by
    have h1 : (2 * f * S) ^ 2 = f ^ 2 * (∑ i, x i * ∑ a, ∑ b, z a * slice T i a b * z b) ^ 2 := by
      rw [hS2]; ring
    rw [h1]
    calc f ^ 2 * (∑ i, x i * ∑ a, ∑ b, z a * slice T i a b * z b) ^ 2
        ≤ f ^ 2 * ((opNorm (oddM T) + 2 * dmax T) * Z ^ 2) := by
          gcongr; exact hCS.trans hQ
      _ = (opNorm (oddM T) + 2 * dmax T) * (f * Z) ^ 2 := by ring
      _ ≤ (opNorm (oddM T) + 2 * dmax T) * 1 := by gcongr
      _ = _ := mul_one _
  have habs := Real.abs_le_sqrt hfin
  rw [hS1, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Nat.factorial (2 * q + 1) : ℝ))]
  have : |2 * f * S| = 2 * f * |S| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * f)]
  rw [this] at habs
  have hc : (0:ℝ) ≤ (Nat.factorial (2 * q + 1) : ℝ) / (2 * f) := by positivity
  calc (Nat.factorial (2 * q + 1) : ℝ) * |S|
      = ((Nat.factorial (2 * q + 1) : ℝ) / (2 * f)) * (2 * f * |S|) := by field_simp
    _ ≤ _ := by gcongr

end SparseTensorInj.Certify

open SparseTensorInj.Certify in
theorem solution (q n : ℕ) (hq : 1 ≤ q) (T : Tensor (2 * q + 1) n) (hT : IsSymmetric T) :
    injNorm T ≤ oddCert T := by
  have hnn : 0 ≤ oddCert T := by
    unfold oddCert frobNorm
    positivity
  unfold injNorm
  refine Real.iSup_le (fun x => ?_) hnn
  have hx : ∑ i, x.1 i ^ 2 = 1 := x.2
  rw [tensor_decomp T x.1]
  refine (abs_add_le _ _).trans ?_
  unfold oddCert
  have h1 := key_bound hq T hT x.1 hx
  have h2 := frob_bound (T - zeroRepeated T) x.1 hx
  linarith
