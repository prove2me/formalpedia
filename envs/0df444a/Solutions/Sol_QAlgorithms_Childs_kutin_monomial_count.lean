-- Prove2me | solution 1 for QAlgorithms.Childs.kutin_monomial_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T21:34:13.47859+00:00
-- url     : https://prove2.me/submissions/5d8fa9d5-0c10-4353-a97a-380ff3220152

import Definitions.Def_QAlgorithms_Defs_Polynomial
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.Polynomial.Pochhammer
set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped BigOperators Classical

namespace KutinCountProof

private noncomputable def splitEmbedding {A B : Type*} (i : A ↪ B) :
    A ⊕ ↥(Set.range i)ᶜ ≃ B := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective i i.injective) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)

private noncomputable def restrictEquiv {A B : Type*} [Fintype B] (i : A ↪ B) :
    Equiv.Perm B ≃ Σ e : A ↪ B, ↥(Set.range i)ᶜ ↪ ↥(Set.range e)ᶜ := by
  classical
  exact (Equiv.embeddingEquivOfFinite B).symm.trans
    ((Equiv.embeddingCongr (splitEmbedding i).symm (Equiv.refl B)).trans
      Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted)

private lemma restrictEquiv_fst {A B : Type*} [Fintype B] (i : A ↪ B)
    (p : Equiv.Perm B) : (restrictEquiv i p).1 = i.trans p.toEmbedding := by
  classical
  rfl

private lemma perm_sum_restrict {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (i : A ↪ B) (F : (A ↪ B) → ℝ) :
    ∑ p : Equiv.Perm B, F (i.trans p.toEmbedding) =
      ((Fintype.card B - Fintype.card A).factorial : ℝ) * ∑ e : A ↪ B, F e := by
  classical
  have hr (e : A ↪ B) : Fintype.card ↥(Set.range e)ᶜ =
      Fintype.card B - Fintype.card A := by
    rw [Fintype.card_compl_set, Fintype.card_range]
  calc
    _ = ∑ q : (Σ e : A ↪ B, ↥(Set.range i)ᶜ ↪ ↥(Set.range e)ᶜ), F q.1 :=
      Fintype.sum_equiv (restrictEquiv i) _ _ (fun p => congrArg F (restrictEquiv_fst i p).symm)
    _ = _ := by
      rw [Fintype.sum_sigma, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq,
        hr, Nat.descFactorial_self]

private noncomputable def fiberEmbeddingEquiv {A B C D : Type*} (q : A → C)
    (x : B → D) (v : C ↪ D) :
    {e : A ↪ B // ∀ a, x (e a) = v (q a)} ≃
      (∀ j : C, {a : A // q a = j} ↪ {b : B // x b = v j}) := by
  classical
  refine
    { toFun := fun e j =>
        ⟨fun a => ⟨e.1 a.1, (e.2 a.1).trans (congrArg v a.2)⟩,
          fun a b hab => Subtype.ext (e.1.injective (congrArg Subtype.val hab))⟩
      invFun := fun f => ⟨⟨fun a => (f (q a) ⟨a, rfl⟩).1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro a b hab
    have hq : q a = q b := by
      apply v.injective
      exact (f (q a) ⟨a, rfl⟩).2.symm.trans
        ((congrArg x hab).trans (f (q b) ⟨b, rfl⟩).2)
    have transport (j k : C) (hjk : j = k) (aa : {a : A // q a = j})
        (bb : {a : A // q a = k})
        (he : (f j aa).1 = (f k bb).1) : aa.1 = bb.1 := by
      subst k
      exact congrArg Subtype.val ((f j).injective (Subtype.ext he))
    exact transport _ _ hq ⟨a, rfl⟩ ⟨b, rfl⟩ hab
  · intro a
    exact (f (q a) ⟨a, rfl⟩).2
  · intro e
    apply Subtype.ext
    ext a
    rfl
  · intro f
    funext j
    ext a
    rcases a with ⟨a, rfl⟩
    rfl

private lemma count_fiber_embeddings {A B C D : Type*} [Fintype A] [Fintype B]
    [Fintype C] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (q : A → C) (x : B → D) (v : C ↪ D) :
    Fintype.card {e : A ↪ B // ∀ a, x (e a) = v (q a)} =
      ∏ j : C, (Fintype.card {b : B // x b = v j}).descFactorial
        (Fintype.card {a : A // q a = j}) := by
  classical
  rw [Fintype.card_congr (fiberEmbeddingEquiv q x v), Fintype.card_pi]
  simp only [Fintype.card_embedding_eq]

private lemma perm_pattern {n : ℕ} {A J : Type*} [Fintype A] [Fintype J] [DecidableEq J]
    (i : A ↪ Fin n) (l : J ↪ Fin n) (q : A → J) (x : Fin n → Fin n) :
    (∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      if ∀ a, τ (x (σ (i a))) = l (q a) then (1 : ℝ) else 0) =
    ((n - Fintype.card A).factorial : ℝ) *
    ((n - Fintype.card J).factorial : ℝ) *
    ∑ v : J ↪ Fin n, ∏ j : J,
      ((Fintype.card {b : Fin n // x b = v j}).descFactorial
        (Fintype.card {a : A // q a = j}) : ℝ) := by
  classical
  have hs (σ : Equiv.Perm (Fin n)) :
      (∑ τ : Equiv.Perm (Fin n),
        if ∀ a, τ (x (σ (i a))) = l (q a) then (1 : ℝ) else 0) =
      ((n - Fintype.card J).factorial : ℝ) *
      ∑ v : J ↪ Fin n, if ∀ a, x (σ (i a)) = v (q a) then 1 else 0 := by
    calc
      _ = ∑ τ : Equiv.Perm (Fin n),
          if ∀ a, x (σ (i a)) = τ (l (q a)) then (1 : ℝ) else 0 := by
        exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _
          (fun τ => by
            change (if ∀ a, τ (x (σ (i a))) = l (q a) then (1 : ℝ) else 0) =
              (if ∀ a, x (σ (i a)) = τ.symm (l (q a)) then 1 else 0)
            congr 1
            exact propext (forall_congr' fun a => (τ.eq_symm_apply).symm))
      _ = _ := by
        simpa only [Fintype.card_fin, Function.Embedding.trans_apply,
          Equiv.toEmbedding_apply] using (perm_sum_restrict l
          (fun v => if ∀ a, x (σ (i a)) = v (q a) then (1 : ℝ) else 0))
  have hc (v : J ↪ Fin n) :
      (∑ e : A ↪ Fin n, if ∀ a, x (e a) = v (q a) then (1 : ℝ) else 0) =
      ∏ j : J, ((Fintype.card {b : Fin n // x b = v j}).descFactorial
        (Fintype.card {a : A // q a = j}) : ℝ) := by
    rw [← Nat.cast_prod, ← count_fiber_embeddings q x v]
    simp [Fintype.card_subtype]
  calc
    _ = ((n - Fintype.card J).factorial : ℝ) *
        ∑ v : J ↪ Fin n, ∑ σ : Equiv.Perm (Fin n),
          if ∀ a, x (σ (i a)) = v (q a) then 1 else 0 := by
      simp_rw [hs]
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = ((n - Fintype.card J).factorial : ℝ) *
        ∑ v : J ↪ Fin n, ((n - Fintype.card A).factorial : ℝ) *
          ∏ j : J, ((Fintype.card {b : Fin n // x b = v j}).descFactorial
            (Fintype.card {a : A // q a = j}) : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      calc
        _ = ((n - Fintype.card A).factorial : ℝ) *
            ∑ e : A ↪ Fin n, if ∀ a, x (e a) = v (q a) then 1 else 0 := by
          simpa only [Fintype.card_fin, Function.Embedding.trans_apply,
            Equiv.toEmbedding_apply] using (perm_sum_restrict i
              (fun e => if ∀ a, x (e a) = v (q a) then (1 : ℝ) else 0))
        _ = _ := by rw [hc]
    _ = _ := by rw [← Finset.mul_sum]; ring


private noncomputable def partitionEmbeddingEquiv {J B : Type*} [Fintype J] [DecidableEq J]
    (U : Finset J) (L H : Finset B) (hd : Disjoint L H) :
    {v : J ↪ B // (∀ j ∈ U, v j ∈ L) ∧ (∀ j ∉ U, v j ∈ H)} ≃
      (↥U ↪ ↥L) × (↥(Finset.univ \ U) ↪ H) := by
  classical
  let merge (f : (↥U ↪ ↥L) × (↥(Finset.univ \ U) ↪ H)) : J → B :=
    fun j => if hj : j ∈ U then (f.1 ⟨j, hj⟩).1 else (f.2 ⟨j, by simp [hj]⟩).1
  have hm (f : (↥U ↪ ↥L) × (↥(Finset.univ \ U) ↪ H)) : Function.Injective (merge f) := by
    intro j k he
    by_cases hj : j ∈ U <;> by_cases hk : k ∈ U
    · exact congrArg Subtype.val
        (f.1.injective (Subtype.ext (by simpa only [merge, dif_pos hj, dif_pos hk] using he)))
    · have h1 := (f.1 ⟨j, hj⟩).2
      have h2 := (f.2 ⟨k, by simp [hk]⟩).2
      have he' : (f.1 ⟨j, hj⟩).1 = (f.2 ⟨k, by simp [hk]⟩).1 := by
        simpa only [merge, dif_pos hj, dif_neg hk] using he
      exact False.elim ((Finset.disjoint_left.mp hd) h1 (he' ▸ h2))
    · have h1 := (f.2 ⟨j, by simp [hj]⟩).2
      have h2 := (f.1 ⟨k, hk⟩).2
      have he' : (f.2 ⟨j, by simp [hj]⟩).1 = (f.1 ⟨k, hk⟩).1 := by
        simpa only [merge, dif_neg hj, dif_pos hk] using he
      exact False.elim ((Finset.disjoint_left.mp hd) h2 (he' ▸ h1))
    · exact congrArg Subtype.val
        (f.2.injective (Subtype.ext (by simpa only [merge, dif_neg hj, dif_neg hk] using he)))
  refine
    { toFun := fun v =>
        (⟨fun j => ⟨v.1 j, v.2.1 j j.2⟩,
          fun j k he => Subtype.ext (v.1.injective (congrArg Subtype.val he))⟩,
         ⟨fun j => ⟨v.1 j, v.2.2 j (Finset.mem_sdiff.mp j.2).2⟩,
          fun j k he => Subtype.ext (v.1.injective (congrArg Subtype.val he))⟩)
      invFun := fun f => ⟨⟨merge f, hm f⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro j hj
      simpa only [Function.Embedding.coeFn_mk, merge, dif_pos hj] using (f.1 ⟨j, hj⟩).2
    · intro j hj
      simpa only [Function.Embedding.coeFn_mk, merge, dif_neg hj] using (f.2 ⟨j, by simp [hj]⟩).2
  · intro v
    apply Subtype.ext
    ext j
    by_cases hj : j ∈ U <;> simp [merge, hj, Function.Embedding.coeFn_mk] <;> rfl
  · intro f
    apply Prod.ext
    · ext j
      simp [merge]
    · ext j
      simp [merge, (Finset.mem_sdiff.mp j.2).2]

private lemma count_partition_embeddings {J B : Type*} [Fintype J] [Fintype B] [DecidableEq J] [DecidableEq B]
    (U : Finset J) (L H : Finset B) (hd : Disjoint L H) :
    Fintype.card {v : J ↪ B // (∀ j ∈ U, v j ∈ L) ∧ (∀ j ∉ U, v j ∈ H)} =
      L.card.descFactorial U.card * H.card.descFactorial (Finset.univ \ U).card := by
  classical
  rw [Fintype.card_congr (partitionEmbeddingEquiv U L H hd), Fintype.card_prod]
  simp only [Fintype.card_embedding_eq, Fintype.card_coe]

private lemma weighted_embeddings {J B : Type*} [Fintype J] [Fintype B] [DecidableEq J] [DecidableEq B]
    (L H : Finset B) (hd : Disjoint L H) (w : J → B → ℝ) (a b : J → ℝ)
    (hL : ∀ j z, z ∈ L → w j z = a j)
    (hH : ∀ j z, z ∈ H → w j z = b j)
    (h0 : ∀ j z, z ∉ L → z ∉ H → w j z = 0) :
    (∑ v : J ↪ B, ∏ j : J, w j (v j)) =
      ∑ U : Finset J,
        (L.card.descFactorial U.card : ℝ) *
        (H.card.descFactorial (Finset.univ \ U).card : ℝ) *
        (∏ j ∈ U, a j) * ∏ j ∈ Finset.univ \ U, b j := by
  classical
  let P (U : Finset J) (v : J ↪ B) :=
    (∀ j ∈ U, v j ∈ L) ∧ (∀ j ∉ U, v j ∈ H)
  have split (v : J ↪ B) :
      (∏ j : J, w j (v j)) =
      ∑ U : Finset J, if P U v then ∏ j : J, w j (v j) else 0 := by
    by_cases hg : ∀ j, v j ∈ L ∨ v j ∈ H
    · let U := Finset.univ.filter (fun j => v j ∈ L)
      have hu : P U v := by
        constructor
        · intro j hj; exact (Finset.mem_filter.mp hj).2
        · intro j hj
          exact (hg j).resolve_left (by simpa [U] using hj)
      have unique (V : Finset J) (hv : P V v) : V = U := by
        ext j
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hj => hv.1 j hj, fun hj => by
          by_contra hn
          exact (Finset.disjoint_left.mp hd) hj (hv.2 j hn)⟩
      rw [Finset.sum_eq_single U]
      · simp [hu]
      · intro V _ hne
        simp only [if_neg (fun hv => hne (unique V hv))]
      · simp
    · obtain ⟨j, hj⟩ := not_forall.mp hg
      have hjL : v j ∉ L := fun hh => hj (Or.inl hh)
      have hjH : v j ∉ H := fun hh => hj (Or.inr hh)
      have hp : (∏ j : J, w j (v j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (h0 j (v j) hjL hjH)
      rw [hp]
      symm
      apply Finset.sum_eq_zero
      intro U _
      simp only [ite_self]
  calc
    _ = ∑ v : J ↪ B, ∑ U : Finset J,
        if P U v then ∏ j : J, w j (v j) else 0 :=
      Finset.sum_congr rfl (fun v _ => split v)
    _ = _ := ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _
  have val (v : J ↪ B) (hv : P U v) :
      (∏ j : J, w j (v j)) = (∏ j ∈ U, a j) * ∏ j ∈ Finset.univ \ U, b j := by
    calc
      _ = (∏ j ∈ U, w j (v j)) * ∏ j ∈ Finset.univ \ U, w j (v j) := by
        rw [mul_comm, Finset.prod_sdiff (Finset.subset_univ U)]
      _ = _ := by
        congr 1
        · exact Finset.prod_congr rfl (fun j hj => hL j (v j) (hv.1 j hj))
        · exact Finset.prod_congr rfl (fun j hj =>
            hH j (v j) (hv.2 j (Finset.mem_sdiff.mp hj).2))
  calc
    _ = ∑ v : J ↪ B, if P U v then
        (∏ j ∈ U, a j) * (∏ j ∈ Finset.univ \ U, b j) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs with hv
      · exact val v hv
      · rfl
    _ = (Fintype.card {v : J ↪ B // P U v} : ℝ) *
        ((∏ j ∈ U, a j) * ∏ j ∈ Finset.univ \ U, b j) := by
      rw [Fintype.card_subtype, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      rw [show Fintype.card {v : J ↪ B // P U v} = _ from
        count_partition_embeddings U L H hd, Nat.cast_mul]
      ring

private noncomputable def kutinDomain (n m a b : ℕ)
    (h : QAlgorithms.ValidKutinTriple n m a b) :
    ((Fin (m / a) × Fin a) ⊕ (Fin ((n-m) / b) × Fin b)) ≃ Fin n :=
  ((Equiv.sumCongr
    (finProdFinEquiv.trans (finCongr (Nat.div_mul_cancel h.2.2.2.1)))
    ((finProdFinEquiv.trans (finCongr (Nat.div_mul_cancel h.2.2.2.2))).trans
      Fin.revPerm)).trans finSumFinEquiv).trans
    (finCongr (Nat.add_sub_of_le h.1))

private lemma kutinDomain_low (n m a b : ℕ)
    (h : QAlgorithms.ValidKutinTriple n m a b) (j : Fin (m/a)) (r : Fin a) :
    (kutinDomain n m a b h (Sum.inl (j,r))).val = r.val + a * j.val := rfl

private lemma kutinDomain_high (n m a b : ℕ)
    (h : QAlgorithms.ValidKutinTriple n m a b) (j : Fin ((n-m)/b)) (r : Fin b) :
    (kutinDomain n m a b h (Sum.inr (j,r))).val =
      m + (n-m-1-(r.val+b*j.val)) := by
  change m + (n-m-(r.val+b*j.val+1)) = _
  omega

private lemma kutin_val {n m a b : ℕ}
    (h : QAlgorithms.ValidKutinTriple n m a b) (p : Fin n) :
    (QAlgorithms.kutinInput n m a b p).val =
      if p.val < m then p.val / a else n - 1 - (n - 1 - p.val) / b := by
  have ha : 0 < a := h.2.1
  have hb : 0 < b := h.2.2.1
  have hp := p.isLt
  have hpa := Nat.div_le_self p.val a
  have hpb := Nat.div_le_self (n-1-p.val) b
  have hn : 0 < n := Nat.zero_lt_of_lt hp
  unfold QAlgorithms.kutinInput
  simp only
  by_cases hm : p.val < m
  · rw [if_pos (by omega)]
    have he : p.val + 1 + a - 1 = p.val + a := by omega
    rw [he, Nat.add_div_right _ ha, if_pos hm]
    simp only [Nat.add_sub_cancel]
    exact Nat.min_eq_left (hpa.trans (Nat.le_pred_of_lt hp))
  · rw [if_neg (by omega), if_neg hm]
    have he : n - (p.val + 1) = n - 1 - p.val := by omega
    rw [he]
    rw [Nat.sub_right_comm n _ 1, Nat.min_eq_left (Nat.sub_le _ _)]

private lemma kutin_low_eval {n m a b : ℕ}
    (h : QAlgorithms.ValidKutinTriple n m a b) (j : Fin (m/a)) (r : Fin a) :
    (QAlgorithms.kutinInput n m a b (kutinDomain n m a b h (Sum.inl (j,r)))).val = j.val := by
  have ha : 0 < a := h.2.1
  have hbound : r.val + a*j.val < m := by
    have := (finProdFinEquiv (j,r)).isLt
    change r.val + a*j.val < (m/a)*a at this
    simpa only [Nat.div_mul_cancel h.2.2.2.1] using this
  rw [kutin_val h, kutinDomain_low, if_pos hbound,
    Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt r.isLt, Nat.zero_add]

private lemma kutin_high_eval {n m a b : ℕ}
    (h : QAlgorithms.ValidKutinTriple n m a b) (j : Fin ((n-m)/b)) (r : Fin b) :
    (QAlgorithms.kutinInput n m a b (kutinDomain n m a b h (Sum.inr (j,r)))).val =
      n - 1 - j.val := by
  have hb : 0 < b := h.2.2.1
  have hbound : r.val + b*j.val < n-m := by
    have := (finProdFinEquiv (j,r)).isLt
    change r.val + b*j.val < ((n-m)/b)*b at this
    simpa only [Nat.div_mul_cancel h.2.2.2.2] using this
  rw [kutin_val h, kutinDomain_high, if_neg (by omega)]
  have he : n-1-(m+(n-m-1-(r.val+b*j.val))) = r.val+b*j.val := by omega
  rw [he, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt r.isLt, Nat.zero_add]

private def lowEmb (n m a : ℕ) (hm : m ≤ n) : Fin (m/a) ↪ Fin n :=
  Fin.castLEEmb ((Nat.div_le_self m a).trans hm)

private def highEmb (n m b : ℕ) : Fin ((n-m)/b) ↪ Fin n :=
  (Fin.castLEEmb ((Nat.div_le_self (n-m) b).trans (Nat.sub_le n m))).trans
    (Fin.revPerm.toEmbedding)

private lemma card_product_fiber {K A Y : Type*} [Fintype K] [Fintype A] [DecidableEq Y]
    (l : K ↪ Y) (z : Y) :
    Fintype.card {p : K × A // l p.1 = z} =
      if z ∈ Set.range l then Fintype.card A else 0 := by
  classical
  by_cases hz : z ∈ Set.range l
  · obtain ⟨k,rfl⟩ := hz
    rw [if_pos (Set.mem_range_self k)]
    apply Fintype.card_congr
    refine
      { toFun := fun p => p.1.2
        invFun := fun a => ⟨(k,a), rfl⟩
        left_inv := ?_
        right_inv := fun _ => rfl }
    intro p
    apply Subtype.ext
    apply Prod.ext
    · exact (l.injective p.2).symm
    · rfl
  · rw [if_neg hz]
    have : IsEmpty {p : K × A // l p.1 = z} :=
      ⟨fun p => hz ⟨p.1.1, p.2⟩⟩
    exact Fintype.card_eq_zero

private lemma block_fiber_card {K T A B X Y : Type*}
    [Fintype K] [Fintype T] [Fintype A] [Fintype B] [Fintype X] [DecidableEq Y]
    (d : (K × A) ⊕ (T × B) ≃ X) (l : K ↪ Y) (r : T ↪ Y) (f : X → Y)
    (hl : ∀ j u, f (d (Sum.inl (j,u))) = l j)
    (hr : ∀ j u, f (d (Sum.inr (j,u))) = r j) (z : Y) :
    Fintype.card {p : X // f p = z} =
      (if z ∈ Set.range l then Fintype.card A else 0) +
      (if z ∈ Set.range r then Fintype.card B else 0) := by
  classical
  calc
    _ = Fintype.card {p : (K × A) ⊕ (T × B) // f (d p) = z} :=
      (Fintype.card_congr (Equiv.subtypeEquivOfSubtype d)).symm
    _ = Fintype.card {p : K × A // l p.1 = z} +
        Fintype.card {p : T × B // r p.1 = z} := by
      rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
      congr 1
      · exact Fintype.card_congr (Equiv.subtypeEquivRight (fun p => by rw [hl]))
      · exact Fintype.card_congr (Equiv.subtypeEquivRight (fun p => by rw [hr]))
    _ = _ := by rw [card_product_fiber, card_product_fiber]

private lemma kutin_profile {n m a b : ℕ} (h : QAlgorithms.ValidKutinTriple n m a b) :
    ∃ L H : Finset (Fin n), Disjoint L H ∧ L.card = m/a ∧ H.card = (n-m)/b ∧
      (∀ z ∈ L, Fintype.card {p : Fin n // QAlgorithms.kutinInput n m a b p = z} = a) ∧
      (∀ z ∈ H, Fintype.card {p : Fin n // QAlgorithms.kutinInput n m a b p = z} = b) ∧
      (∀ z, z ∉ L → z ∉ H →
        Fintype.card {p : Fin n // QAlgorithms.kutinInput n m a b p = z} = 0) := by
  classical
  let l := lowEmb n m a h.1
  let r := highEmb n m b
  let L := Finset.univ.map l
  let H := Finset.univ.map r
  have hL (z : Fin n) : z ∈ L ↔ z ∈ Set.range l := by simp [L, Set.mem_range]
  have hH (z : Fin n) : z ∈ H ↔ z ∈ Set.range r := by simp [H, Set.mem_range]
  have hd : Disjoint L H := by
    apply Finset.disjoint_left.mpr
    intro z hzL hzH
    obtain ⟨j, rfl⟩ := (hL z).mp hzL
    obtain ⟨k, he⟩ := (hH (l j)).mp hzH
    have hv := congrArg Fin.val he
    have hj := j.isLt
    have hk := k.isLt
    have hka := Nat.div_le_self m a
    have hkb := Nat.div_le_self (n-m) b
    have hlv : (l j).val = j.val := rfl
    have hrv : (r k).val = n-(k.val+1) := rfl
    rw [hrv, hlv] at hv
    omega
  have hf (z : Fin n) :
      Fintype.card {p : Fin n // QAlgorithms.kutinInput n m a b p = z} =
        (if z ∈ L then a else 0) + (if z ∈ H then b else 0) := by
    have hl (j : Fin (m/a)) (u : Fin a) :
        QAlgorithms.kutinInput n m a b (kutinDomain n m a b h (Sum.inl (j,u))) = l j := by
      apply Fin.ext
      exact kutin_low_eval h j u
    have hr (j : Fin ((n-m)/b)) (u : Fin b) :
        QAlgorithms.kutinInput n m a b (kutinDomain n m a b h (Sum.inr (j,u))) = r j := by
      apply Fin.ext
      change _ = n-(j.val+1)
      exact (kutin_high_eval h j u).trans (by omega)
    simpa only [← hL, ← hH, Fintype.card_fin] using
      (block_fiber_card (kutinDomain n m a b h) l r (QAlgorithms.kutinInput n m a b) hl hr z)
  refine ⟨L,H,hd,?_,?_,?_,?_,?_⟩
  · simp [L]
  · simp [H]
  · intro z hz
    rw [hf, if_pos hz, if_neg (fun hh => Finset.disjoint_left.mp hd hz hh), Nat.add_zero]
  · intro z hz
    rw [hf, if_pos hz, if_neg (fun hh => Finset.disjoint_left.mp hd hh hz), Nat.zero_add]
  · intro z hzL hzH
    rw [hf, if_neg hzL, if_neg hzH]

private lemma fall_nat (n k : ℕ) :
    (∏ q ∈ Finset.range k, ((n : ℝ) - q)) = (n.descFactorial k : ℝ) := by
  rw [← descPochhammer_eval_eq_prod_range,
    descPochhammer_eval_eq_descFactorial]

private lemma subtype_partition_sum {X : Type*} [DecidableEq X]
    (J : Finset X) (k t : ℕ) (a b : X → ℝ) :
    (∑ U : Finset J,
      (k.descFactorial U.card : ℝ) *
      (t.descFactorial (Finset.univ \ U).card : ℝ) *
      (∏ j ∈ U, a j) * ∏ j ∈ Finset.univ \ U, b j) =
    ∑ U ∈ J.powerset,
      (k.descFactorial U.card : ℝ) *
      (t.descFactorial (J \ U).card : ℝ) *
      (∏ j ∈ U, a j) * ∏ j ∈ J \ U, b j := by
  classical
  let emb : J ↪ X := Function.Embedding.subtype _
  have hmap : Finset.univ.map emb = J := by
    ext j
    simp [emb]
  refine Finset.sum_bij (fun U _ => U.map emb) ?_ ?_ ?_ ?_
  · intro U _
    apply Finset.mem_powerset.mpr
    intro j hj
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hj
    exact u.2
  · intro U _ V _ he
    exact Finset.map_injective emb he
  · intro U hU
    refine ⟨U.subtype (· ∈ J), Finset.mem_univ _, ?_⟩
    exact Finset.subtype_map_of_mem (Finset.mem_powerset.mp hU)
  · intro U _
    have hdiff : (Finset.univ \ U).map emb = J \ U.map emb := by
      rw [Finset.map_sdiff, hmap]
    rw [← hdiff]
    simp only [Finset.card_map, Finset.prod_map]
    rfl

end KutinCountProof

open KutinCountProof QAlgorithms

theorem solution (n m a b : ℕ) (h : ValidKutinTriple n m a b)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e.2 = f.2) :
    let J := E.image Prod.snd
    let c := fun j => (E.filter (fun e => e.2 = j)).card
    (((n.factorial : ℝ) ^ 2)⁻¹ *
      ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ∏ e ∈ E, kutinDelta n m a b σ τ e) =
    ((n.descFactorial E.card : ℝ) * (n.descFactorial J.card : ℝ))⁻¹ *
      ∑ U ∈ J.powerset,
        (∏ q ∈ Finset.range U.card, ((m : ℝ) / a - q)) *
        (∏ q ∈ Finset.range (J \ U).card, (((n : ℝ) - m) / b - q)) *
        (∏ j ∈ U, ∏ q ∈ Finset.range (c j), ((a : ℝ) - q)) *
        (∏ j ∈ J \ U, ∏ q ∈ Finset.range (c j), ((b : ℝ) - q)) := by
  classical
  let J := E.image Prod.snd
  let c := fun j => (E.filter (fun e => e.2 = j)).card
  let i : E ↪ Fin n := ⟨fun e => e.1.1, by
    intro e f he
    apply Subtype.ext
    exact Prod.ext he (hE e.1 e.2 f.1 f.2 he)⟩
  let l : J ↪ Fin n := Function.Embedding.subtype _
  let q : E → J := fun e => ⟨e.1.2, Finset.mem_image_of_mem Prod.snd e.2⟩
  have hc (j : J) : Fintype.card {e : E // q e = j} = c j := by
    change _ = (E.filter (fun e => e.2 = j.val)).card
    rw [← Fintype.card_coe (E.filter (fun e => e.2 = j.val))]
    apply Fintype.card_congr
    refine
      { toFun := fun e => ⟨e.1.1, Finset.mem_filter.mpr ⟨e.1.2, ?_⟩⟩
        invFun := fun e => ⟨⟨e.1, (Finset.mem_filter.mp e.2).1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · exact congrArg Subtype.val e.2
    · exact Subtype.ext (Finset.mem_filter.mp e.2).2
  have hcpos (j : J) : 0 < c j := by
    obtain ⟨e, he, hej⟩ := Finset.mem_image.mp j.2
    apply Finset.card_pos.mpr
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hej⟩⟩
  have hevent (σ τ : Equiv.Perm (Fin n)) :
      (∏ e ∈ E, kutinDelta n m a b σ τ e) =
      if ∀ e : E, τ (kutinInput n m a b (σ (i e))) = l (q e) then (1 : ℝ) else 0 := by
    by_cases hh : ∀ e : E, τ (kutinInput n m a b (σ (i e))) = l (q e)
    · rw [if_pos hh]
      apply Finset.prod_eq_one
      intro e he
      exact if_pos (hh ⟨e,he⟩)
    · rw [if_neg hh]
      obtain ⟨e, he⟩ := not_forall.mp hh
      exact Finset.prod_eq_zero e.2 (if_neg he)
  obtain ⟨L,H,hd,hLc,hHc,hLa,hHb,h0⟩ := kutin_profile h
  have hweights :
      (∑ v : J ↪ Fin n, ∏ j : J,
        ((Fintype.card {p : Fin n // kutinInput n m a b p = v j}).descFactorial (c j) : ℝ)) =
      ∑ U ∈ J.powerset,
        ((m/a).descFactorial U.card : ℝ) *
        (((n-m)/b).descFactorial (J \ U).card : ℝ) *
        (∏ j ∈ U, (a.descFactorial (c j) : ℝ)) *
        ∏ j ∈ J \ U, (b.descFactorial (c j) : ℝ) := by
    rw [weighted_embeddings L H hd
      (fun (j : J) z => ((Fintype.card {p : Fin n // kutinInput n m a b p = z}).descFactorial (c j) : ℝ))
      (fun j => (a.descFactorial (c j) : ℝ)) (fun j => (b.descFactorial (c j) : ℝ))
      (fun j z hz => by rw [hLa z hz]) (fun j z hz => by rw [hHb z hz])
      (fun j z hzL hzH => by rw [h0 z hzL hzH, Nat.descFactorial_eq_zero_iff_lt.mpr (hcpos j), Nat.cast_zero])]
    rw [hLc,hHc]
    exact subtype_partition_sum J (m/a) ((n-m)/b)
      (fun j => (a.descFactorial (c j) : ℝ)) (fun j => (b.descFactorial (c j) : ℝ))
  have hraw := perm_pattern i l q (kutinInput n m a b)
  simp_rw [← hevent, hc] at hraw
  simp only [Fintype.card_coe] at hraw
  rw [hweights] at hraw
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by have := h.2.1; omega)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by have := h.2.2.1; omega)
  have hdiva : (m : ℝ)/a = (m/a : ℕ) := (Nat.cast_div h.2.2.2.1 ha0).symm
  have hdivb : ((n : ℝ)-m)/b = ((n-m)/b : ℕ) := by
    rw [← Nat.cast_sub h.1]
    exact (Nat.cast_div h.2.2.2.2 hb0).symm
  change _ = _ * _
  simp_rw [hdiva,hdivb,fall_nat]
  rw [hraw]
  have hEs : E.card ≤ n := by simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective i i.injective
  have hJs : J.card ≤ n := by simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective l l.injective
  have hfE : ((n-E.card).factorial : ℝ) * (n.descFactorial E.card : ℝ) = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hEs
  have hfJ : ((n-J.card).factorial : ℝ) * (n.descFactorial J.card : ℝ) = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hJs
  have hn0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hne : (n.descFactorial E.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hEs).ne'
  have hnj : (n.descFactorial J.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hJs).ne'
  have hnorm : (((n.factorial : ℝ)^2)⁻¹) *
      ((n-E.card).factorial : ℝ) * ((n-J.card).factorial : ℝ) =
      ((n.descFactorial E.card : ℝ)*(n.descFactorial J.card : ℝ))⁻¹ := by
    field_simp [hn0,hne,hnj]
    nlinarith only [congrArg₂ (fun u v : ℝ => u*v) hfE hfJ]
  rw [← mul_assoc, ← mul_assoc, hnorm]

