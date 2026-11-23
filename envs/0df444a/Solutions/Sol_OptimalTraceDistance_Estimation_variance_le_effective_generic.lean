-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.variance_le_effective_generic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T06:33:13.524494+00:00
-- url     : https://prove2.me/submissions/c75090c2-d265-4592-a978-c2b81923dcb7

import Definitions.Def_OptimalTraceDistance_Estimation_Observables
import Definitions.Def_OptimalTraceDistance_Estimation_HoeffdingGen

open scoped BigOperators Matrix Classical ComplexOrder
noncomputable section

namespace OTDHoeff
open Matrix OptimalTraceDistance.Estimation

lemma kron_mul {ι : Type*} [Fintype ι] {r : ℕ} (A B : Fin r → Matrix ι ι ℂ) :
    OptimalSpectrum.Entangled.kronFamily (fun j => A j * B j) =
      OptimalSpectrum.Entangled.kronFamily A * OptimalSpectrum.Entangled.kronFamily B := by
  ext x y
  simp only [OptimalSpectrum.Entangled.kronFamily, mul_apply, Matrix.of_apply]
  have := Fintype.prod_sum (fun (j : Fin r) (c : ι) => A j (x j) c * B j c (y j))
  rw [this]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma kron_conj {ι : Type*} [Fintype ι] {r : ℕ} (A : Fin r → Matrix ι ι ℂ) :
    (OptimalSpectrum.Entangled.kronFamily A)ᴴ =
      OptimalSpectrum.Entangled.kronFamily (fun j => (A j)ᴴ) := by
  ext x y
  simp [OptimalSpectrum.Entangled.kronFamily, conjTranspose_apply, star_prod]

def jinv {k n : ℕ} (e : Fin k ↪ Fin n) {i : Fin n} (h : i ∈ Set.range e) : Fin k := Classical.choose h

lemma e_jinv {k n : ℕ} (e : Fin k ↪ Fin n) {i : Fin n} (h : i ∈ Set.range e) : e (jinv e h) = i :=
  Classical.choose_spec h

lemma jinv_e {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (h : e j ∈ Set.range e) : jinv e h = j :=
  e.injective (e_jinv e h)

lemma sum_cond {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [AddCommMonoid M] (C : Prop) [Decidable C] (a0 : α) (b0 : β) (f : α → β → M) :
    ∑ a, ∑ b, (if C ∧ a0 = a ∧ b0 = b then f a b else 0) = if C then f a0 b0 else 0 := by
  by_cases hC : C
  · simp only [hC, true_and, if_true]
    rw [Finset.sum_eq_single a0 (fun a _ ha => Finset.sum_eq_zero (fun b _ => if_neg (fun h => ha h.1.symm))) (by simp)]
    rw [Finset.sum_eq_single b0 (fun b _ hb => if_neg (fun h => hb h.2.symm)) (by simp)]
    simp
  · simp [hC]


lemma trace_tensor {ι : Type*} [Fintype ι] {k : ℕ} (A : Fin k → Matrix ι ι ℂ) :
    (tensor k A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply]
  exact (Fintype.prod_sum (fun i c => A i c c)).symm

lemma inner_sum_gen {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (e : Fin k ↪ Fin n)
    (M : Fin n → Matrix ι ι ℂ) (a b : Fin k → ι) :
    ∑ x : Fin n → ι, ∑ y : Fin n → ι, (∏ i, M i (x i) (y i)) *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0)) =
      (∏ i ∈ Finset.univ.filter (fun i => i ∉ Set.range e), (M i).trace) * ∏ j, M (e j) (b j) (a j) := by
  set f : Fin n → ι → ι → ℂ := fun i c' c => M i c' c *
    (if h : i ∈ Set.range e then (if c = a (jinv e h) ∧ c' = b (jinv e h) then (1:ℂ) else 0)
      else (if c = c' then 1 else 0)) with hf
  have h1 : ∀ x y : Fin n → ι, (∏ i, M i (x i) (y i)) *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0)) = ∏ i, f i (x i) (y i) := by
    intro x y; rw [← Finset.prod_mul_distrib]
  simp only [h1]
  have h2 : ∀ x : Fin n → ι, ∑ y : Fin n → ι, ∏ i, f i (x i) (y i) = ∏ i, ∑ c, f i (x i) c := by
    intro x; rw [Fintype.prod_sum (fun i c => f i (x i) c)]
  simp only [h2]
  rw [Fintype.prod_sum (fun i c' => ∑ c, f i c' c) |>.symm]
  have h3 : ∀ i, ∑ c', ∑ c, f i c' c =
      if h : i ∈ Set.range e then M i (b (jinv e h)) (a (jinv e h)) else (M i).trace := by
    intro i
    by_cases h : i ∈ Set.range e
    · simp only [hf, dif_pos h]
      rw [Finset.sum_eq_single (b (jinv e h))]
      · rw [Finset.sum_eq_single (a (jinv e h))]
        · simp
        · intro c _ hc; simp [hc]
        · simp
      · intro c' _ hc'; refine Finset.sum_eq_zero (fun c _ => ?_); simp [hc']
      · simp
    · simp only [hf, dif_neg h]
      have : ∀ c', ∑ c, M i c' c * (if c = c' then (1:ℂ) else 0) = M i c' c' := by
        intro c'; simp
      simp only [this]; rfl
  simp only [h3]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ Set.range e), mul_comm]
  congr 1
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi; rw [dif_neg hi.2]
  · have hfm : Finset.univ.filter (fun i => i ∈ Set.range e) = Finset.univ.map e := by
      ext i; simp
    rw [hfm, Finset.prod_map]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [dif_pos (Set.mem_range_self j), jinv_e]

lemma trace_embed_gen {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (e : Fin k ↪ Fin n)
    (M : Fin n → Matrix ι ι ℂ) (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    (tensor n M * embed e H).trace =
      (∏ i ∈ Finset.univ.filter (fun i => i ∉ Set.range e), (M i).trace) *
        (tensor k (fun j => M (e j)) * H).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tensor,
    OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply]
  -- expand H (y∘e) (x∘e) as a sum over a b
  have hexp : ∀ x y : Fin n → ι, embed e H y x = ∑ a : Fin k → ι, ∑ b : Fin k → ι, H a b *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then 1 else 0)
        else (if y i = x i then 1 else 0)) := by
    intro x y
    have hprod : ∀ a b : Fin k → ι, (∏ i, (if h : i ∈ Set.range e then
        (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0))) =
        if (∀ i, i ∉ Set.range e → y i = x i) ∧ (y ∘ e = a) ∧ (x ∘ e = b) then 1 else 0 := by
      intro a b
      have : ∀ i, (if h : i ∈ Set.range e then
          (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
          else (if y i = x i then 1 else 0)) =
          if (if h : i ∈ Set.range e then (y i = a (jinv e h) ∧ x i = b (jinv e h)) else y i = x i)
            then 1 else 0 := by
        intro i; split_ifs <;> simp_all
      simp only [this, Fintype.prod_boole]
      congr 1
      apply propext
      constructor
      · intro hall
        refine ⟨fun i hi => ?_, ?_, ?_⟩
        · have := hall i; rwa [dif_neg hi] at this
        · funext j
          have := hall (e j); rw [dif_pos (Set.mem_range_self j), jinv_e] at this; exact this.1
        · funext j
          have := hall (e j); rw [dif_pos (Set.mem_range_self j), jinv_e] at this; exact this.2
      · rintro ⟨h1, rfl, rfl⟩ i
        by_cases hi : i ∈ Set.range e
        · rw [dif_pos hi]
          simp only [Function.comp_apply, e_jinv]; exact ⟨trivial, trivial⟩
        · rw [dif_neg hi]; exact h1 i hi
    simp only [hprod, mul_ite, mul_one, mul_zero]
    rw [sum_cond (∀ i, i ∉ Set.range e → y i = x i) (y ∘ e) (x ∘ e) (fun a b => H a b)]
    rfl
  simp only [hexp, Finset.mul_sum]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  conv_lhs => enter [2, x, 2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  have : ∀ x y : Fin n → ι, (∏ i, M i (x i) (y i)) * (H a b *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0))) = H a b * ((∏ i, M i (x i) (y i)) *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0))) := fun x y => by ring
  simp only [this, ← Finset.mul_sum]
  rw [inner_sum_gen e M a b]
  simp only [Matrix.trace, Matrix.diag]; ring


open Matrix OptimalTraceDistance.Estimation



lemma powerState_eq {ι : Type*} [Fintype ι] (τ : Matrix ι ι ℂ) (k : ℕ) :
    powerState τ k = tensor k (fun _ => τ) := rfl

lemma tensor_conj {ι : Type*} [Fintype ι] {k : ℕ} (A : Fin k → Matrix ι ι ℂ) :
    (tensor k A)ᴴ = tensor k (fun i => (A i)ᴴ) := kron_conj A

lemma tensor_mul {ι : Type*} [Fintype ι] {k : ℕ} (A B : Fin k → Matrix ι ι ℂ) :
    tensor k A * tensor k B = tensor k (fun i => A i * B i) := (kron_mul A B).symm

lemma inner_tensor {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : Matrix ι ι ℂ) {k : ℕ}
    (A B : Fin k → Matrix ι ι ℂ) :
    weightedInner τ k (tensor k A) (tensor k B) = ∏ i, (τ * (A i)ᴴ * B i).trace := by
  unfold weightedInner
  rw [powerState_eq, tensor_conj, tensor_mul, tensor_mul, trace_tensor]

/-- number of injections `Fin k ↪ Fin n` whose range contains `S` -/
def Ncount (k n : ℕ) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun e : Fin k ↪ Fin n => ∀ i ∈ S, i ∈ Set.range e)).card

lemma Ncount_perm {k n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    Ncount k n (S.map σ.toEmbedding) = Ncount k n S := by
  unfold Ncount
  refine Finset.card_nbij' (fun e => e.trans σ.symm.toEmbedding) (fun e => e.trans σ.toEmbedding)
    ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he ⊢
    intro i hi
    obtain ⟨y, hy⟩ := he (σ i) (Finset.mem_map_of_mem _ hi)
    exact ⟨y, by simp [hy]⟩
  · intro e he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he ⊢
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨x, hx, rfl⟩ := hi
    obtain ⟨y, hy⟩ := he x hx
    exact ⟨y, by simp [hy]⟩
  · intro e _; ext; simp
  · intro e _; ext; simp

lemma exists_perm_map {n : ℕ} (S S' : Finset (Fin n)) (h : S.card = S'.card) :
    ∃ σ : Equiv.Perm (Fin n), S.map σ.toEmbedding = S' := by
  let e0 : {x // x ∈ S} ≃ {x // x ∈ S'} :=
    (S.equivFin).trans ((finCongr h).trans S'.equivFin.symm)
  refine ⟨e0.extendSubtype, ?_⟩
  ext y
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Equiv.extendSubtype_mem e0 x hx
  · intro hy
    refine ⟨(e0.symm ⟨y, hy⟩).1, (e0.symm ⟨y, hy⟩).2, ?_⟩
    rw [Equiv.extendSubtype_apply_of_mem e0 _ (e0.symm ⟨y, hy⟩).2]
    simp

lemma Ncount_card_eq {k n : ℕ} (S S' : Finset (Fin n)) (h : S.card = S'.card) :
    Ncount k n S = Ncount k n S' := by
  obtain ⟨σ, hσ⟩ := exists_perm_map S S' h
  rw [← hσ, Ncount_perm]

lemma Ncount_sum (k n j : ℕ) :
    ∑ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)), Ncount k n S =
      Fintype.card (Fin k ↪ Fin n) * Nat.choose k j := by
  unfold Ncount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [← Finset.card_univ, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Finset.card_filter]
  have : (Finset.powersetCard j Finset.univ).filter (fun S : Finset (Fin n) => ∀ i ∈ S, i ∈ Set.range e) =
      Finset.powersetCard j (Finset.univ.map e) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hc, hS⟩
      refine ⟨fun i hi => ?_, hc⟩
      obtain ⟨y, hy⟩ := hS i hi
      exact Finset.mem_map.2 ⟨y, Finset.mem_univ _, hy⟩
    · rintro ⟨hS, hc⟩
      refine ⟨hc, fun i hi => ?_⟩
      obtain ⟨y, -, hy⟩ := Finset.mem_map.1 (hS hi)
      exact ⟨y, hy⟩
  rw [this, Finset.card_powersetCard, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma Ncount_eq {k n j : ℕ} (S : Finset (Fin n)) (hS : S.card = j) :
    Ncount k n S * Nat.choose n j = Fintype.card (Fin k ↪ Fin n) * Nat.choose k j := by
  rw [← Ncount_sum k n j]
  have : ∀ S' ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)), Ncount k n S' = Ncount k n S := by
    intro S' hS'
    rw [Finset.mem_powersetCard] at hS'
    exact Ncount_card_eq S' S (by rw [hS'.2, hS])
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]


lemma herm_smul_real' {ι : Type*} [Fintype ι] (c : ℝ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ((c : ℂ) • A).IsHermitian := by
  unfold IsHermitian at hA ⊢; rw [conjTranspose_smul, hA]; simp [Complex.conj_ofReal]

lemma herm_finsum {ι κ : Type*} [Fintype ι] (S : Finset κ) (A : κ → Matrix ι ι ℂ)
    (h : ∀ k ∈ S, (A k).IsHermitian) : (∑ k ∈ S, A k).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_sum]
  exact Finset.sum_congr rfl (fun k hk => h k hk)

lemma embed_herm {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (e : Fin k ↪ Fin n)
    {H : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hH : H.IsHermitian) : (embed e H).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, embed]
  have hc : (∀ i, i ∉ Set.range e → y i = x i) ↔ (∀ i, i ∉ Set.range e → x i = y i) :=
    ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩
  by_cases h : ∀ i, i ∉ Set.range e → x i = y i
  · rw [if_pos (hc.mpr h), if_pos h]
    have := congrFun (congrFun hH (x ∘ e)) (y ∘ e)
    simpa [conjTranspose_apply] using this
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, star_zero]

lemma uStat_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    {H : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hH : H.IsHermitian) : (uStatistic n k H).IsHermitian := by
  unfold uStatistic
  have hs : (∑ e : Fin k ↪ Fin n, embed e H).IsHermitian :=
    herm_finsum _ _ (fun e _ => embed_herm e hH)
  unfold IsHermitian at hs ⊢
  rw [conjTranspose_smul, hs]; congr 1; simp


section fourier
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ}
  {A : Type*} [Fintype A] [DecidableEq A] {a0 : A} {F : A → Matrix ι ι ℂ}

lemma inner_basis (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0)
    {k : ℕ} (α β : Fin k → A) :
    weightedInner τ k (tensor k (fun i => F (α i))) (tensor k (fun i => F (β i))) =
      if α = β then 1 else 0 := by
  rw [inner_tensor]
  simp only [horth]
  rw [Fintype.prod_boole]
  by_cases h : α = β
  · simp [h]
  · rw [if_neg h, if_neg]; intro h'; exact h (funext h')

lemma tensor_sum {k : ℕ} (c : Fin k → A → ℂ) :
    tensor k (fun i => ∑ a, c i a • F a) =
      ∑ α : Fin k → A, (∏ i, c i (α i)) • tensor k (fun i => F (α i)) := by
  ext x y
  simp only [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum (fun i a => c i a * F a (x i) (y i))]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma weightedInner_add_right {k : ℕ} (X Y Z : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k X (Y + Z) = weightedInner τ k X Y + weightedInner τ k X Z := by
  unfold weightedInner; rw [Matrix.mul_add, Matrix.trace_add]

lemma weightedInner_smul_right {k : ℕ} (X Y : Matrix (Fin k → ι) (Fin k → ι) ℂ) (c : ℂ) :
    weightedInner τ k X (c • Y) = c * weightedInner τ k X Y := by
  unfold weightedInner; rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

lemma weightedInner_sum_right {k : ℕ} {S : Type*} [Fintype S] (X : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (Y : S → Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k X (∑ s, Y s) = ∑ s, weightedInner τ k X (Y s) := by
  unfold weightedInner; rw [Matrix.mul_sum, Matrix.trace_sum]

lemma weightedInner_sum_left {k : ℕ} {S : Type*} [Fintype S] (X : S → Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (Y : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k (∑ s, X s) Y = ∑ s, weightedInner τ k (X s) Y := by
  unfold weightedInner
  rw [Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]

lemma weightedInner_smul_left {k : ℕ} (X Y : Matrix (Fin k → ι) (Fin k → ι) ℂ) (c : ℂ) :
    weightedInner τ k (c • X) Y = star c * weightedInner τ k X Y := by
  unfold weightedInner
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

lemma stdBasis_tensor {k : ℕ} (x y : Fin k → ι) :
    tensor k (fun i => Matrix.single (x i) (y i) (1:ℂ)) = Matrix.single x y (1:ℂ) := by
  ext u v
  simp only [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, Matrix.single_apply]
  rw [Fintype.prod_boole]
  by_cases h1 : x = u <;> by_cases h2 : y = v
  · subst h1; subst h2; simp
  · rw [if_neg, if_neg]
    · rintro ⟨-, h⟩; exact h2 h
    · intro h; exact h2 (funext fun i => (h i).2)
  · rw [if_neg, if_neg]
    · rintro ⟨h, -⟩; exact h1 h
    · intro h; exact h1 (funext fun i => (h i).1)
  · rw [if_neg, if_neg]
    · rintro ⟨h, -⟩; exact h1 h
    · intro h; exact h1 (funext fun i => (h i).1)

omit [DecidableEq A] in
lemma sum_pair {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [AddCommMonoid M] (a0 : α) (b0 : β) (f : α → β → M) :
    ∑ a, ∑ b, (if a = a0 ∧ b = b0 then f a b else 0) = f a0 b0 := by
  rw [Finset.sum_eq_single a0 (fun a _ ha => Finset.sum_eq_zero (fun b _ => if_neg (fun h => ha h.1)))
    (by simp)]
  rw [Finset.sum_eq_single b0 (fun b _ hb => if_neg (fun h => hb h.2)) (by simp)]
  simp

lemma expansion_exists (hspan : ∀ B : Matrix ι ι ℂ, ∃ c : A → ℂ, B = ∑ a, c a • F a) {k : ℕ}
    (G : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    ∃ d : (Fin k → A) → ℂ, G = ∑ α, d α • tensor k (fun i => F (α i)) := by
  choose c hc using hspan
  have hG : G = ∑ x : Fin k → ι, ∑ y : Fin k → ι, G x y • Matrix.single x y (1:ℂ) := by
    ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    exact (sum_pair u v (fun x y => G x y)).symm
  refine ⟨fun α => ∑ x : Fin k → ι, ∑ y : Fin k → ι, G x y *
    ∏ i, c (Matrix.single (x i) (y i) (1:ℂ)) (α i), ?_⟩
  conv_lhs => rw [hG]
  simp only [← stdBasis_tensor]
  conv_lhs => enter [2, x, 2, y]; rw [show tensor k (fun i => Matrix.single (x i) (y i) (1:ℂ)) =
      tensor k (fun i => ∑ a, c (Matrix.single (x i) (y i) (1:ℂ)) a • F a) from by
        congr 1; funext i; exact hc _]
  simp only [tensor_sum, Finset.smul_sum, smul_smul, Finset.sum_smul]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

lemma coeff_eq (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0) {k : ℕ}
    (d : (Fin k → A) → ℂ) (β : Fin k → A) :
    weightedInner τ k (tensor k (fun i => F (β i))) (∑ α, d α • tensor k (fun i => F (α i))) = d β := by
  rw [weightedInner_sum_right]
  simp only [weightedInner_smul_right, inner_basis horth]
  simp [eq_comm]

lemma expansion (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0)
    (hspan : ∀ B : Matrix ι ι ℂ, ∃ c : A → ℂ, B = ∑ a, c a • F a) {k : ℕ}
    (G : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    G = ∑ α : Fin k → A, weightedInner τ k (tensor k (fun i => F (α i))) G •
      tensor k (fun i => F (α i)) := by
  obtain ⟨d, hd⟩ := expansion_exists hspan G
  conv_rhs => rw [hd]
  simp only [coeff_eq horth]
  exact hd

lemma powerState_herm (hτ : τ.IsHermitian) (k : ℕ) : (powerState τ k).IsHermitian := by
  unfold IsHermitian; rw [powerState_eq, tensor_conj, hτ.eq]

lemma inner_swap (hτ : τ.IsHermitian) {k : ℕ} (X Y : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k X Y = star (weightedInner τ k Y X) := by
  unfold weightedInner
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, (powerState_herm hτ k).eq, Matrix.trace_mul_comm]
  try simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]

lemma parseval (hτ : τ.IsHermitian) (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0)
    (hspan : ∀ B : Matrix ι ι ℂ, ∃ c : A → ℂ, B = ∑ a, c a • F a) {k : ℕ}
    (G : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k G G = ∑ α : Fin k → A,
      ((‖weightedInner τ k (tensor k (fun i => F (α i))) G‖^2 : ℝ) : ℂ) := by
  set c := fun α : Fin k → A => weightedInner τ k (tensor k (fun i => F (α i))) G with hc
  have hG := expansion horth hspan G
  nth_rewrite 2 [hG]
  rw [weightedInner_sum_right]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [weightedInner_smul_right]
  have : weightedInner τ k G (tensor k (fun i => F (α i))) = star (c α) := by
    rw [hc]; exact inner_swap hτ _ _
  rw [this, Complex.star_def, hc]
  simp only []
  rw [Complex.mul_conj']
  push_cast; rfl


lemma coeff_embed (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0)
    (hF0 : F a0 = 1) {k n : ℕ} (e : Fin k ↪ Fin n) (α : Fin n → A)
    (h : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ n (tensor n (fun i => F (α i))) (embed e h) =
      (if ∀ i, i ∉ Set.range e → α i = a0 then 1 else 0) *
        weightedInner τ k (tensor k (fun j => F (α (e j)))) h := by
  unfold weightedInner
  rw [powerState_eq, tensor_conj, tensor_mul, trace_embed_gen, powerState_eq, tensor_conj, tensor_mul]
  congr 1
  have h1 : ∀ a, (τ * (F a)ᴴ).trace = if a = a0 then 1 else 0 := by
    intro a; rw [← horth a a0, hF0, Matrix.mul_one]
  simp only [h1]
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · intro hall i hi; exact hall i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  · intro hall i hi; exact hall i (Finset.mem_filter.1 hi).2

lemma permOp_mul' {k : ℕ} (π π' : Equiv.Perm (Fin k)) :
    permutationOp (ι := ι) π * permutationOp π' = permutationOp (π * π') := by
  ext x y
  simp only [Matrix.mul_apply, permutationOp, OptimalSpectrum.Entangled.permOp, Matrix.of_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (y ∘ ⇑π'.symm)]
  · simp only [if_true]
    have : y ∘ ⇑(π * π').symm = (y ∘ ⇑π'.symm) ∘ ⇑π.symm := by
      funext a; simp [Equiv.Perm.mul_def]
    rw [this]
  · intro u _ hu; rw [if_neg hu]
  · simp

lemma permOp_conj {k : ℕ} (π : Equiv.Perm (Fin k)) :
    (permutationOp (ι := ι) π)ᴴ = permutationOp π⁻¹ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, permutationOp, OptimalSpectrum.Entangled.permOp,
    Matrix.of_apply, apply_ite star, star_one, star_zero]
  have : (y = x ∘ ⇑π.symm) ↔ (x = y ∘ ⇑(π⁻¹).symm) := by
    constructor
    · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
    · rintro rfl; funext i; simp [Equiv.Perm.inv_def]
  by_cases h : y = x ∘ ⇑π.symm
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]

lemma permOp_unitary {k : ℕ} (π : Equiv.Perm (Fin k)) :
    permutationOp (ι := ι) π * (permutationOp π)ᴴ = 1 := by
  rw [permOp_conj, permOp_mul', mul_inv_cancel]
  ext x y
  simp only [permutationOp, OptimalSpectrum.Entangled.permOp, Matrix.of_apply, Matrix.one_apply]
  have : (Equiv.symm (1 : Equiv.Perm (Fin k)) : Fin k → Fin k) = id := by
    funext i; rfl
  rw [this, Function.comp_id]

lemma tensor_perm {k : ℕ} (G : Fin k → Matrix ι ι ℂ) (π : Equiv.Perm (Fin k)) :
    (permutationOp (ι := ι) π)ᴴ * tensor k G * permutationOp π = tensor k (fun i => G (π i)) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permutationOp,
    OptimalSpectrum.Entangled.permOp, Matrix.of_apply, tensor,
    OptimalSpectrum.Entangled.kronFamily]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  first
  | (rw [← Equiv.prod_comp π.symm (fun i => G (π i) (x i) (y i))]; simp)
  | (rw [← Equiv.prod_comp π (fun j => G j ((x ∘ ⇑π.symm) j) ((y ∘ ⇑π.symm) j))]; simp)

lemma inner_perm (hτ : τ.IsHermitian) {k : ℕ} (h : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin k), permutationOp π * h * (permutationOp π)ᴴ = h)
    (β : Fin k → A) (π : Equiv.Perm (Fin k)) :
    weightedInner τ k (tensor k (fun i => F (β (π i)))) h =
      weightedInner τ k (tensor k (fun i => F (β i))) h := by
  unfold weightedInner
  rw [← tensor_perm (fun i => F (β i)) π]
  set P := permutationOp (ι := ι) π
  set T := tensor k (fun i => F (β i))
  have hP : P * Pᴴ = 1 := permOp_unitary π
  have hτP : powerState τ k = Pᴴ * powerState τ k * P := by
    rw [powerState_eq, tensor_perm]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  conv_lhs => rw [hτP]
  calc (Pᴴ * powerState τ k * P * (Pᴴ * (Tᴴ * P)) * h).trace
      = (Pᴴ * (powerState τ k * (P * Pᴴ) * Tᴴ * (P * h))).trace := by simp only [Matrix.mul_assoc]
    _ = (powerState τ k * Tᴴ * (P * h * Pᴴ)).trace := by
        rw [hP, Matrix.mul_one, Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hsym π]


def glueEquiv {α : Type*} {k j : ℕ} (hjk : j ≤ k) : (Fin j → α) × (Fin (k-j) → α) ≃ (Fin k → α) where
  toFun p := glueGen p.1 p.2
  invFun u := (fun i => u (Fin.castLE hjk i), fun i => u ⟨i.val + j, by omega⟩)
  left_inv p := by
    obtain ⟨x, z⟩ := p
    ext i
    · simp [glueGen, Fin.castLE]
    · simp only [glueGen]
      rw [dif_neg (by simp)]
      congr 1; ext; simp
  right_inv u := by
    funext i
    simp only [glueGen]
    split_ifs with h
    · rfl
    · congr 1; ext; simp; omega

lemma prod_split {M : Type*} [CommMonoid M] {k j : ℕ} (hjk : j ≤ k) (f : Fin k → M) :
    ∏ i, f i = (∏ i : Fin j, f (Fin.castLE hjk i)) * ∏ i : Fin (k-j), f ⟨i.val + j, by omega⟩ := by
  let e : Fin j ⊕ Fin (k-j) ≃ Fin k := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hjk))
  have he1 : ∀ i : Fin j, e (Sum.inl i) = Fin.castLE hjk i := by intro i; ext; simp [e]
  have he2 : ∀ i : Fin (k-j), e (Sum.inr i) = ⟨i.val + j, by omega⟩ := by
    intro i; ext; simp [e]; omega
  rw [← Fintype.prod_equiv e (fun s => f (e s)) f (fun _ => rfl), Fintype.prod_sum_type]
  simp only [he1, he2]

lemma glue_castLE {α : Type*} {k j : ℕ} (hjk : j ≤ k) (x : Fin j → α) (z : Fin (k-j) → α) (i : Fin j) :
    glueGen (k := k) x z (Fin.castLE hjk i) = x i := by
  simp [glueGen, Fin.castLE]

lemma glue_shift {α : Type*} {k j : ℕ} (x : Fin j → α) (z : Fin (k-j) → α) (i : Fin (k-j)) :
    glueGen (k := k) x z ⟨i.val + j, by omega⟩ = z i := by
  simp only [glueGen]; rw [dif_neg (by simp)]; congr 1; ext; simp

lemma inner_contraction (hF0 : F a0 = 1) {k j : ℕ} (hjk : j ≤ k) (a : Fin j → A)
    (h : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k (tensor k (fun i => F (glueGen (k := k) a (fun _ => a0) i))) h =
      weightedInner τ j (tensor j (fun i => F (a i))) (contractionGen τ k j h) := by
  unfold weightedInner
  rw [powerState_eq, tensor_conj, tensor_mul, powerState_eq, tensor_conj, tensor_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tensor,
    OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, contractionGen, powerState]
  rw [← (glueEquiv (α := ι) hjk).sum_comp, Fintype.sum_prod_type]
  simp only [← (glueEquiv (α := ι) hjk).sum_comp (fun v => _ * h v _), Fintype.sum_prod_type]
  simp only [glueEquiv, Equiv.coe_fn_mk]
  have hprod : ∀ (u1 v1 : Fin j → ι) (u2 v2 : Fin (k-j) → ι),
      (∏ l, ∑ c, τ (glueGen (k := k) u1 u2 l) c * (F (glueGen (k := k) a (fun _ => a0) l))ᴴ c
        (glueGen (k := k) v1 v2 l)) =
      (∏ i, ∑ c, τ (u1 i) c * (F (a i))ᴴ c (v1 i)) * ∏ i, τ (u2 i) (v2 i) := by
    intro u1 v1 u2 v2
    rw [prod_split hjk]
    congr 1
    · simp only [glue_castLE]
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [glue_shift, hF0, Matrix.conjTranspose_one, Matrix.one_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hprod]
  refine Finset.sum_congr rfl (fun u1 _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v1 _ => ?_)
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v2 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u2 _ => ?_)
  ring


lemma perm_glue {n k j : ℕ} (hjk : j ≤ k) (α : Fin n → A) (S : Finset (Fin n))
    (hSdef : S = Finset.univ.filter (fun i => α i ≠ a0)) (hS : S.card = j)
    (e : Fin k ↪ Fin n) (he : ∀ i ∈ S, i ∈ Set.range e) :
    ∃ π : Equiv.Perm (Fin k), ∀ l, α (e (π l)) =
      glueGen (k := k) (fun i => α (S.orderEmbOfFin hS i)) (fun _ => a0) l := by
  set s := S.orderEmbOfFin hS
  have hsS : ∀ i, s i ∈ S := fun i => Finset.orderEmbOfFin_mem S hS i
  choose p hp using fun i => he (s i) (hsS i)
  have hpinj : Function.Injective p := by
    intro i i' h
    have : s i = s i' := by rw [← hp i, ← hp i', h]
    exact s.injective this
  let e1 : {l : Fin k // l.val < j} ≃ Fin j :=
    { toFun := fun l => ⟨l.1.val, l.2⟩
      invFun := fun i => ⟨Fin.castLE hjk i, by simp⟩
      left_inv := fun l => by ext; simp
      right_inv := fun i => by ext; simp }
  let e0 : {l : Fin k // l.val < j} ≃ {l : Fin k // l ∈ Set.range p} :=
    e1.trans (Equiv.ofInjective p hpinj)
  refine ⟨e0.extendSubtype, fun l => ?_⟩
  by_cases hl : l.val < j
  · rw [Equiv.extendSubtype_apply_of_mem e0 l hl]
    simp only [glueGen, dif_pos hl, e0, e1, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.ofInjective_apply]
    rw [hp]
  · have hnot := (e0.toCompl ⟨l, hl⟩).2
    rw [Equiv.extendSubtype_apply_of_not_mem e0 l hl]
    simp only [glueGen, dif_neg hl]
    by_contra hne
    have hmS : e (e0.toCompl ⟨l, hl⟩ : Fin k) ∈ S := by
      rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hne⟩
    have : e (e0.toCompl ⟨l, hl⟩ : Fin k) ∈ Set.range s := by
      rw [Finset.range_orderEmbOfFin S hS]; exact hmS
    obtain ⟨i, hi⟩ := this
    apply hnot
    refine ⟨i, e.injective ?_⟩
    rw [hp, hi]

lemma coeff_uStat (hτ : τ.IsHermitian)
    (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0)
    (hF0 : F a0 = 1) {k n : ℕ} (hkn : k ≤ n) (h : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin k), permutationOp π * h * (permutationOp π)ᴴ = h)
    (α : Fin n → A) (S : Finset (Fin n)) (hSdef : S = Finset.univ.filter (fun i => α i ≠ a0))
    {j : ℕ} (hS : S.card = j) (hjk : j ≤ k) :
    weightedInner τ n (tensor n (fun i => F (α i))) (uStatistic n k h) =
      ((Nat.choose k j : ℂ) / (Nat.choose n j : ℂ)) *
        weightedInner τ j (tensor j (fun i => F (α (S.orderEmbOfFin hS i)))) (contractionGen τ k j h) := by
  unfold uStatistic
  rw [weightedInner_smul_right, weightedInner_sum_right]
  simp only [coeff_embed horth hF0]
  set V := weightedInner τ j (tensor j (fun i => F (α (S.orderEmbOfFin hS i)))) (contractionGen τ k j h)
  have hterm : ∀ e : Fin k ↪ Fin n,
      (if ∀ i, i ∉ Set.range e → α i = a0 then (1:ℂ) else 0) *
        weightedInner τ k (tensor k (fun j => F (α (e j)))) h =
      if ∀ i ∈ S, i ∈ Set.range e then V else 0 := by
    intro e
    have hiff : (∀ i, i ∉ Set.range e → α i = a0) ↔ (∀ i ∈ S, i ∈ Set.range e) := by
      constructor
      · intro hall i hi; by_contra hne; rw [hSdef] at hi; simp at hi; exact hi (hall i hne)
      · intro hall i hi; by_contra hne; exact hi (hall i (by rw [hSdef]; simpa using hne))
    by_cases hc : ∀ i ∈ S, i ∈ Set.range e
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
      obtain ⟨π, hπ⟩ := perm_glue hjk α S hSdef hS e hc
      rw [← inner_perm hτ h hsym (fun l => α (e l)) π]
      simp only [hπ]
      exact inner_contraction hF0 hjk _ h
    · rw [if_neg (fun h' => hc (hiff.1 h')), if_neg hc, zero_mul]
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hN := Ncount_eq (k := k) S hS
  have hcard : (Finset.univ.filter (fun e : Fin k ↪ Fin n => ∀ i ∈ S, i ∈ Set.range e)).card =
      Ncount k n S := rfl
  rw [hcard]
  have hpos : (Fintype.card (Fin k ↪ Fin n) : ℂ) ≠ 0 := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast (Nat.descFactorial_pos.2 hkn).ne'
  have hnj : (Nat.choose n j : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hjk.trans hkn)).ne'
  have hN' : (Ncount k n S : ℂ) * (Nat.choose n j : ℂ) =
      (Fintype.card (Fin k ↪ Fin n) : ℂ) * (Nat.choose k j : ℂ) := by exact_mod_cast hN
  field_simp
  linear_combination V * hN'


lemma coeff_uStat_zero (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0)
    (hF0 : F a0 = 1) {k n : ℕ} (h : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (α : Fin n → A) (S : Finset (Fin n)) (hSdef : S = Finset.univ.filter (fun i => α i ≠ a0))
    (hk : k < S.card) :
    weightedInner τ n (tensor n (fun i => F (α i))) (uStatistic n k h) = 0 := by
  unfold uStatistic
  rw [weightedInner_smul_right, weightedInner_sum_right]
  simp only [coeff_embed horth hF0]
  rw [Finset.sum_eq_zero, mul_zero]
  intro e _
  rw [if_neg, zero_mul]
  intro hall
  have hsub : S ⊆ Finset.univ.map e := by
    intro i hi
    by_contra hne
    rw [hSdef, Finset.mem_filter] at hi
    exact hi.2 (hall i (fun ⟨y, hy⟩ => hne (Finset.mem_map.2 ⟨y, Finset.mem_univ _, hy⟩)))
  have := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at this
  omega

lemma tensor_const_one {k : ℕ} : tensor k (fun _ : Fin k => (1 : Matrix ι ι ℂ)) = 1 := by
  ext x y
  simp only [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.prod_boole]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, if_neg]; intro h'; exact h (funext h')

/-- total version of the order embedding -/
def ordF {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (j : ℕ) (i : Fin j) : Fin n :=
  if h : S.card = j then S.orderEmbOfFin h i else ⟨0, hn⟩


lemma weightedInner_finsum_right {k : ℕ} {S : Type*} (T : Finset S)
    (X : Matrix (Fin k → ι) (Fin k → ι) ℂ) (Y : S → Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    weightedInner τ k X (∑ s ∈ T, Y s) = ∑ s ∈ T, weightedInner τ k X (Y s) := by
  unfold weightedInner; rw [Matrix.mul_sum, Matrix.trace_sum]

lemma coeff_G (hτ : τ.IsHermitian)
    (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0)
    (hF0 : F a0 = 1) {n D : ℕ} (hn : 0 < n) (hD : D ≤ n)
    (h : (k : ℕ) → Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hsym : ∀ k ∈ Finset.Icc 1 D, ∀ π : Equiv.Perm (Fin k),
      permutationOp π * h k * (permutationOp π)ᴴ = h k)
    (f₀ : ℝ) (α : Fin n → A) (hα : α ≠ fun _ => a0) :
    weightedInner τ n (tensor n (fun i => F (α i)))
      ((f₀ : ℂ) • 1 + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)) =
    if (Finset.univ.filter (fun i => α i ≠ a0)).card ≤ D then
      ((Nat.choose n (Finset.univ.filter (fun i => α i ≠ a0)).card : ℂ))⁻¹ *
        weightedInner τ _ (tensor _ (fun i => F (α (ordF hn (Finset.univ.filter (fun i => α i ≠ a0))
          (Finset.univ.filter (fun i => α i ≠ a0)).card i))))
          (effectiveKernelGen τ D h (Finset.univ.filter (fun i => α i ≠ a0)).card)
    else 0 := by
  set S := Finset.univ.filter (fun i => α i ≠ a0) with hSdef
  set j := S.card with hj
  have hj1 : 1 ≤ j := by
    rw [hj, Nat.one_le_iff_ne_zero]
    intro h0
    apply hα
    funext i
    by_contra hne
    have : i ∈ S := by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hne⟩
    rw [Finset.card_eq_zero] at h0
    rw [h0] at this; simp at this
  rw [weightedInner_add_right, weightedInner_smul_right]
  have h1 : weightedInner τ n (tensor n (fun i => F (α i))) 1 = 0 := by
    rw [← tensor_const_one, ← hF0]
    rw [inner_basis horth α (fun _ => a0), if_neg hα]
  rw [h1, mul_zero, zero_add, weightedInner_finsum_right]
  have hterm : ∀ k ∈ Finset.Icc 1 D,
      weightedInner τ n (tensor n (fun i => F (α i))) (uStatistic n k (h k)) =
      if j ≤ k then ((Nat.choose k j : ℂ) / (Nat.choose n j : ℂ)) *
        weightedInner τ j (tensor j (fun i => F (α (ordF hn S j i)))) (contractionGen τ k j (h k))
      else 0 := by
    intro k hk
    have hkn : k ≤ n := (Finset.mem_Icc.1 hk).2.trans hD
    by_cases hjk : j ≤ k
    · rw [if_pos hjk, coeff_uStat hτ horth hF0 hkn (h k) (hsym k hk) α S hSdef rfl hjk]
      congr 3
      funext i
      simp only [ordF, dif_pos (show S.card = j from rfl)]
    · rw [if_neg hjk]
      exact coeff_uStat_zero horth hF0 (h k) α S hSdef (by omega)
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_filter]
  have hfil : (Finset.Icc 1 D).filter (fun k => j ≤ k) = Finset.Icc j D := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hfil]
  by_cases hjD : j ≤ D
  · rw [if_pos hjD]
    unfold effectiveKernelGen
    rw [weightedInner_finsum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [weightedInner_smul_right]; ring
  · rw [if_neg hjD]
    have : Finset.Icc j D = ∅ := by ext k; simp; omega
    rw [this, Finset.sum_empty]


lemma ordF_inj {n j : ℕ} (hn : 0 < n) (α β : Fin n → A)
    (hS : Finset.univ.filter (fun i => α i ≠ a0) = Finset.univ.filter (fun i => β i ≠ a0))
    (hj : (Finset.univ.filter (fun i => α i ≠ a0)).card = j)
    (ha : (fun i => α (ordF hn (Finset.univ.filter (fun i => α i ≠ a0)) j i)) =
      (fun i => β (ordF hn (Finset.univ.filter (fun i => β i ≠ a0)) j i))) : α = β := by
  funext i
  by_cases hi : i ∈ Finset.univ.filter (fun i => α i ≠ a0)
  · have hr := Finset.range_orderEmbOfFin _ hj
    have : i ∈ Set.range ((Finset.univ.filter (fun i => α i ≠ a0)).orderEmbOfFin hj) := by
      rw [hr]; exact hi
    obtain ⟨m, hm⟩ := this
    have := congrFun ha m
    simp only [ordF, dif_pos hj, ← hS] at this
    rw [hm] at this; exact this
  · have hi' : i ∉ Finset.univ.filter (fun i => β i ≠ a0) := by rw [← hS]; exact hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi hi'
    rw [hi, hi']

theorem var_fourier (hτ : τ.PosSemidef)
    (horth : ∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0)
    (hspan : ∀ B : Matrix ι ι ℂ, ∃ c : A → ℂ, B = ∑ a, c a • F a)
    (hF0 : F a0 = 1) {n D : ℕ} (hn : 0 < n) (hD : D ≤ n)
    (h : (k : ℕ) → Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hherm : ∀ k ∈ Finset.Icc 1 D, (h k).IsHermitian)
    (hsym : ∀ k ∈ Finset.Icc 1 D, ∀ π : Equiv.Perm (Fin k),
      permutationOp π * h k * (permutationOp π)ᴴ = h k)
    (f₀ : ℝ) :
    variance τ n ((f₀ : ℂ) • 1 + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)) ≤
      ∑ j ∈ Finset.Icc 1 D, ((Nat.choose n j : ℝ))⁻¹ *
        weightedNormSq τ j (effectiveKernelGen τ D h j) := by
  have hτH : τ.IsHermitian := hτ.1
  set G := (f₀ : ℂ) • (1 : Matrix (Fin n → ι) (Fin n → ι) ℂ) + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)
    with hGdef
  have hGH : G.IsHermitian :=
    (herm_smul_real' f₀ isHermitian_one).add (herm_finsum _ _ (fun k hk => uStat_herm n k (hherm k hk)))
  set c := fun α : Fin n → A => weightedInner τ n (tensor n (fun i => F (α i))) G with hc
  set α0 : Fin n → A := fun _ => a0 with hα0
  have hpar := parseval hτH horth hspan G
  -- variance as a sum over nonzero multi-indices
  have hvar : variance τ n G = ∑ α ∈ Finset.univ.erase α0, ‖c α‖^2 := by
    have h1 : tr (powerState τ n * G^2) = ∑ α, ‖c α‖^2 := by
      have : (powerState τ n * G^2).trace = weightedInner τ n G G := by
        unfold weightedInner; rw [hGH.eq, sq, Matrix.mul_assoc]
      unfold tr; rw [this, hpar, Complex.re_sum]
      simp only [← Complex.ofReal_pow, Complex.ofReal_re]
      rfl
    have h2 : c α0 = (powerState τ n * G).trace := by
      simp only [hc, hα0, hF0, tensor_const_one]
      unfold weightedInner; rw [Matrix.conjTranspose_one, Matrix.mul_one]
    have h3 : (c α0).im = 0 := by
      rw [h2]
      have : star (powerState τ n * G).trace = (powerState τ n * G).trace := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hGH.eq,
          (powerState_herm hτH n).eq, Matrix.trace_mul_comm]
      exact Complex.conj_eq_iff_im.1 this
    have h4 : tr (powerState τ n * G) = (c α0).re := by unfold tr; rw [h2]
    unfold variance
    rw [h1, h4, ← Finset.add_sum_erase _ _ (Finset.mem_univ α0)]
    have : ‖c α0‖^2 = (c α0).re^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, h3]; ring
    rw [this]; ring
  rw [hvar]
  set Sf : (Fin n → A) → Finset (Fin n) := fun α => Finset.univ.filter (fun i => α i ≠ a0) with hSf
  set jf : (Fin n → A) → ℕ := fun α => (Sf α).card with hjf
  set bf : (j : ℕ) → (Fin j → A) → ℝ := fun j a =>
    ‖weightedInner τ j (tensor j (fun i => F (a i))) (effectiveKernelGen τ D h j)‖^2 with hbf
  set af : (Fin n → A) → (j : ℕ) → Fin j → A := fun α j i => α (ordF hn (Sf α) j i) with haf
  have hcα : ∀ α ∈ Finset.univ.erase α0, ‖c α‖^2 =
      if jf α ∈ Finset.Icc 1 D then (((Nat.choose n (jf α) : ℝ))⁻¹)^2 * bf (jf α) (af α (jf α)) else 0 := by
    intro α hα
    have hne : α ≠ fun _ => a0 := Finset.ne_of_mem_erase hα
    have hj1 : 1 ≤ jf α := by
      simp only [hjf, hSf]
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      apply hne; funext i; by_contra hi
      rw [Finset.card_eq_zero] at h0
      have : i ∈ Finset.univ.filter (fun i => α i ≠ a0) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩
      rw [h0] at this; simp at this
    simp only [hc]
    rw [coeff_G hτH horth hF0 hn hD h hsym f₀ α hne]
    by_cases hjD : jf α ≤ D
    · rw [if_pos hjD, if_pos (Finset.mem_Icc.2 ⟨hj1, hjD⟩), norm_mul, mul_pow, norm_inv]
      simp only [hbf, haf, hjf, hSf]
      congr 2
      simp
    · rw [if_neg hjD, if_neg (fun h' => hjD (Finset.mem_Icc.1 h').2)]; simp
  rw [Finset.sum_congr rfl hcα]
  have hnn : ∀ α, 0 ≤ (if jf α ∈ Finset.Icc 1 D then
      (((Nat.choose n (jf α) : ℝ))⁻¹)^2 * bf (jf α) (af α (jf α)) else 0) := by
    intro α; split_ifs <;> positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun α _ _ => hnn α)) ?_
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to (g := jf) (t := Finset.Icc 1 D)
    (fun α hα => (Finset.mem_filter.1 hα).2)]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hj' := Finset.mem_Icc.1 hj
  have hfib : ∀ α ∈ (Finset.univ.filter (fun α => jf α ∈ Finset.Icc 1 D)).filter (fun α => jf α = j),
      (((Nat.choose n (jf α) : ℝ))⁻¹)^2 * bf (jf α) (af α (jf α)) =
        (((Nat.choose n j : ℝ))⁻¹)^2 * bf j (af α j) := by
    intro α hα
    have := (Finset.mem_filter.1 hα).2
    rw [this]
  rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
  -- injection into supports × coefficient indices
  set s := (Finset.univ.filter (fun α => jf α ∈ Finset.Icc 1 D)).filter (fun α => jf α = j)
  have hinj : Set.InjOn (fun α => (Sf α, af α j)) s := by
    intro α hα β hβ heq
    simp only [Prod.mk.injEq] at heq
    have hjα : jf α = j := (Finset.mem_filter.1 hα).2
    exact ordF_inj hn α β heq.1 hjα heq.2
  have hsub : s.image (fun α => (Sf α, af α j)) ⊆
      Finset.powersetCard j (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin j → A)) := by
    intro p hp
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hp
    simp only [Finset.mem_product, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_univ, and_true]
    exact (Finset.mem_filter.1 hα).2
  have h1 : ∑ α ∈ s, bf j (af α j) = ∑ p ∈ s.image (fun α => (Sf α, af α j)), bf j p.2 := by
    rw [Finset.sum_image hinj]
  have h2 : ∑ p ∈ s.image (fun α => (Sf α, af α j)), bf j p.2 ≤
      ∑ p ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin j → A)),
        bf j p.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by simp only [hbf]; positivity)
  have h3 : ∑ p ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin j → A)),
      bf j p.2 = (Nat.choose n j : ℝ) * weightedNormSq τ j (effectiveKernelGen τ D h j) := by
    rw [Finset.sum_product]
    simp only []
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    unfold weightedNormSq
    rw [parseval hτH horth hspan, Complex.re_sum]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, hbf]
  have hcpos : (0:ℝ) < Nat.choose n j := by exact_mod_cast Nat.choose_pos (hj'.2.trans hD)
  calc (((Nat.choose n j : ℝ))⁻¹)^2 * ∑ α ∈ s, bf j (af α j)
      ≤ (((Nat.choose n j : ℝ))⁻¹)^2 * ((Nat.choose n j : ℝ) * weightedNormSq τ j (effectiveKernelGen τ D h j)) := by
        gcongr; rw [h1, ← h3]; exact h2
    _ = _ := by field_simp

end fourier


section existence
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sqrt_facts {τ : Matrix ι ι ℂ} (hτ : τ.PosDef) :
    ∃ sq si : Matrix ι ι ℂ, sq.IsHermitian ∧ si.IsHermitian ∧ sq * sq = τ ∧ sq * si = 1 ∧ si * sq = 1 := by
  have hH := hτ.1
  set U := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hpos : ∀ i, 0 < hH.eigenvalues i := hτ.eigenvalues_pos
  set d1 : ι → ℂ := fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)
  set d2 : ι → ℂ := fun i => ((1 / Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)
  refine ⟨U * diagonal d1 * star U, U * diagonal d2 * star U, ?_, ?_, ?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, diagonal_conjTranspose]
    simp only [Matrix.mul_assoc, d1]
    congr 2; ext i j; simp [Matrix.diagonal_apply, Complex.conj_ofReal]
  · unfold IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, diagonal_conjTranspose]
    simp only [Matrix.mul_assoc, d2]
    congr 2; ext i j; simp [Matrix.diagonal_apply, Complex.conj_ofReal]
  · have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    conv_rhs => rw [hspec]
    calc U * diagonal d1 * star U * (U * diagonal d1 * star U)
        = U * (diagonal d1 * (star U * U) * diagonal d1) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hUU, Matrix.mul_one, diagonal_mul_diagonal]
        rw [show (fun i => d1 i * d1 i) = RCLike.ofReal ∘ hH.eigenvalues from by
          funext i; simp only [d1, Function.comp_apply, ← Complex.ofReal_mul]
          rw [Real.mul_self_sqrt (hpos i).le]; rfl]
  · calc U * diagonal d1 * star U * (U * diagonal d2 * star U)
        = U * (diagonal d1 * (star U * U) * diagonal d2) * star U := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hUU, Matrix.mul_one, diagonal_mul_diagonal]
        have : (fun i => d1 i * d2 i) = fun _ => (1:ℂ) := by
          funext i; simp only [d1, d2, ← Complex.ofReal_mul]
          rw [mul_one_div_cancel (Real.sqrt_pos.2 (hpos i)).ne']; simp
        rw [this, diagonal_one, Matrix.mul_one]
        exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  · calc U * diagonal d2 * star U * (U * diagonal d1 * star U)
        = U * (diagonal d2 * (star U * U) * diagonal d1) * star U := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hUU, Matrix.mul_one, diagonal_mul_diagonal]
        have : (fun i => d2 i * d1 i) = fun _ => (1:ℂ) := by
          funext i; simp only [d1, d2, ← Complex.ofReal_mul]
          rw [one_div_mul_cancel (Real.sqrt_pos.2 (hpos i)).ne']; simp
        rw [this, diagonal_one, Matrix.mul_one]
        exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2

theorem fourier_exists {τ : Matrix ι ι ℂ} (hτ : τ.PosDef) (htr : τ.trace = 1) :
    ∃ (p0 : ι × ι) (F : ι × ι → Matrix ι ι ℂ), F p0 = 1 ∧
      (∀ a b, (τ * (F a)ᴴ * F b).trace = if a = b then 1 else 0) ∧
      (∀ B : Matrix ι ι ℂ, ∃ c : ι × ι → ℂ, B = ∑ a, c a • F a) := by
  obtain ⟨sq, si, hsqH, hsiH, hss, hsi, his⟩ := sqrt_facts hτ
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : τ.trace = 0 := by simp [Matrix.trace]
    rw [htr] at this; exact one_ne_zero this
  obtain ⟨i0⟩ := hne
  let vecM : Matrix ι ι ℂ → EuclideanSpace ℂ (ι × ι) := fun X => WithLp.toLp 2 (fun p => X p.1 p.2)
  let unvec : EuclideanSpace ℂ (ι × ι) → Matrix ι ι ℂ := fun v i j => (WithLp.ofLp v) (i, j)
  have hunvec_vec : ∀ X, unvec (vecM X) = X := fun X => rfl
  have hinner : ∀ v w : EuclideanSpace ℂ (ι × ι), inner ℂ v w = ((unvec v)ᴴ * unvec w).trace := by
    intro v w
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      unvec, Pi.star_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    show _ = star (v.ofLp (j, i)) * w.ofLp (j, i)
    ring
  set u := vecM sq with hu
  have hunorm : ‖u‖ = 1 := by
    have h1 : inner ℂ u u = (1:ℂ) := by
      rw [hinner, hunvec_vec, hsqH.eq, hss, htr]
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u
    rw [h1] at h2
    have h3 : ((‖u‖^2 : ℝ) : ℂ) = 1 := by rw [Complex.ofReal_pow]; exact h2.symm
    have : ‖u‖^2 = 1 := by exact_mod_cast h3
    have h0 : 0 ≤ ‖u‖ := norm_nonneg _
    nlinarith
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (ι × ι)) = Fintype.card (ι × ι) :=
    finrank_euclideanSpace
  have hon : Orthonormal ℂ (({(i0, i0)} : Set (ι × ι)).restrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Set.mem_singleton_iff] at ha hb
    subst ha; subst hb
    simp only [if_true]
    rw [inner_self_eq_norm_sq_to_K]
    change ((‖u‖ : ℝ) : ℂ)^2 = 1
    rw [hunorm]; simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hon
  have hb0 : b (i0, i0) = u := hb (i0, i0) (Set.mem_singleton _)
  refine ⟨(i0, i0), fun p => unvec (b p) * si, ?_, ?_, ?_⟩
  · simp only [hb0, hu, hunvec_vec, hsi]
  · intro a c
    have : (τ * (unvec (b a) * si)ᴴ * (unvec (b c) * si)).trace = inner ℂ (b a) (b c) := by
      rw [hinner, ← hss, Matrix.conjTranspose_mul, hsiH.eq]
      calc (sq * sq * (si * (unvec (b a))ᴴ) * (unvec (b c) * si)).trace
          = (sq * (sq * si) * ((unvec (b a))ᴴ * unvec (b c)) * si).trace := by
            simp only [Matrix.mul_assoc]
        _ = ((unvec (b a))ᴴ * unvec (b c) * (si * sq)).trace := by
            rw [hsi, Matrix.mul_one, Matrix.mul_assoc, Matrix.trace_mul_comm]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [his, Matrix.mul_one]
    rw [this, orthonormal_iff_ite.1 b.orthonormal a c]
  · intro B
    refine ⟨fun p => inner ℂ (b p) (vecM (B * sq)), ?_⟩
    have hrep := b.sum_repr' (vecM (B * sq))
    have hlin : ∀ (c : ι × ι → ℂ), unvec (∑ p, c p • b p) = ∑ p, c p • unvec (b p) := by
      intro c; ext i j; simp only [unvec, Matrix.sum_apply]
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun p _ => rfl)
    calc B = unvec (vecM (B * sq)) * si := by rw [hunvec_vec, Matrix.mul_assoc, hsi, Matrix.mul_one]
      _ = unvec (∑ p, inner ℂ (b p) (vecM (B * sq)) • b p) * si := by rw [hrep]
      _ = _ := by rw [hlin, Finset.sum_mul]; simp only [Matrix.smul_mul]

lemma cont_ps {k : ℕ} {M : ℝ → Matrix ι ι ℂ} (hM : Continuous M) :
    Continuous (fun δ => powerState (M δ) k) := by
  apply continuous_matrix
  intro x y
  simp only [powerState, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply]
  exact continuous_finset_prod _ (fun i _ => hM.matrix_elem _ _)

lemma cont_contraction {k j : ℕ} {M : ℝ → Matrix ι ι ℂ} (hM : Continuous M)
    (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    Continuous (fun δ => contractionGen (M δ) k j H) := by
  apply continuous_matrix
  intro x y
  simp only [contractionGen]
  refine continuous_finset_sum _ (fun z _ => continuous_finset_sum _ (fun w _ => ?_))
  exact continuous_const.mul ((cont_ps hM).matrix_elem _ _)

lemma cont_eff {D j : ℕ} {M : ℝ → Matrix ι ι ℂ} (hM : Continuous M)
    (h : (k : ℕ) → Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    Continuous (fun δ => effectiveKernelGen (M δ) D h j) := by
  unfold effectiveKernelGen
  refine continuous_finset_sum _ (fun k _ => ?_)
  apply continuous_matrix
  intro x y
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact continuous_const.mul ((cont_contraction hM (h k)).matrix_elem x y)

theorem variance_le_effectiveG {τ : Matrix ι ι ℂ} (hτ : τ.PosSemidef) (htr : τ.trace = 1)
    {n D : ℕ} (hn : 0 < n) (hD : D ≤ n)
    (h : (k : ℕ) → Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hherm : ∀ k ∈ Finset.Icc 1 D, (h k).IsHermitian)
    (hsym : ∀ k ∈ Finset.Icc 1 D, ∀ π : Equiv.Perm (Fin k),
      permutationOp π * h k * (permutationOp π)ᴴ = h k)
    (f₀ : ℝ) :
    variance τ n ((f₀ : ℂ) • 1 + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)) ≤
      ∑ j ∈ Finset.Icc 1 D, ((Nat.choose n j : ℝ))⁻¹ *
        weightedNormSq τ j (effectiveKernelGen τ D h j) := by
  -- positive definite case
  have hpd_case : ∀ σ : Matrix ι ι ℂ, σ.PosDef → σ.trace = 1 →
      variance σ n ((f₀ : ℂ) • 1 + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)) ≤
        ∑ j ∈ Finset.Icc 1 D, ((Nat.choose n j : ℝ))⁻¹ *
          weightedNormSq σ j (effectiveKernelGen σ D h j) := by
    intro σ hσ hσtr
    obtain ⟨p0, F, hF0, horth, hspan⟩ := fourier_exists hσ hσtr
    exact var_fourier (a0 := p0) hσ.posSemidef horth hspan hF0 hn hD h hherm hsym f₀
  set G := (f₀ : ℂ) • (1 : Matrix (Fin n → ι) (Fin n → ι) ℂ) + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)
  have hm : 0 < Fintype.card ι := by
    rw [Fintype.card_pos_iff]
    by_contra hne; rw [not_nonempty_iff] at hne
    have : τ.trace = 0 := by simp [Matrix.trace]
    rw [htr] at this; exact one_ne_zero this
  set m : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact_mod_cast hm
  set τδ : ℝ → Matrix ι ι ℂ := fun δ => ((1 - δ : ℝ) : ℂ) • τ + ((δ / m : ℝ) : ℂ) • 1 with hτδ
  have hcont : Continuous τδ := by
    simp only [hτδ]
    exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).smul continuous_const).add
      ((Complex.continuous_ofReal.comp (continuous_id.div_const _)).smul continuous_const)
  have h0 : τδ 0 = τ := by simp [hτδ]
  have hgood : ∀ δ ∈ Set.Ioo (0:ℝ) 1, (τδ δ).PosDef ∧ (τδ δ).trace = 1 := by
    intro δ hδ
    obtain ⟨h1, h2⟩ := hδ
    refine ⟨?_, ?_⟩
    · refine Matrix.PosDef.posSemidef_add ?_ ?_
      · exact hτ.smul (by exact_mod_cast (show (0:ℝ) ≤ 1 - δ by linarith))
      · exact Matrix.PosDef.one.smul (by exact_mod_cast (show (0:ℝ) < δ / m by positivity))
    · simp only [hτδ, Matrix.trace_add, Matrix.trace_smul, htr, Matrix.trace_one, smul_eq_mul]
      rw [show ((Fintype.card ι : ℕ) : ℂ) = (m : ℂ) by rw [hmdef]; push_cast; rfl]
      push_cast
      field_simp
      ring
  set fL : ℝ → ℝ := fun δ => variance (τδ δ) n G with hfL
  set fR : ℝ → ℝ := fun δ => ∑ j ∈ Finset.Icc 1 D, ((Nat.choose n j : ℝ))⁻¹ *
      weightedNormSq (τδ δ) j (effectiveKernelGen (τδ δ) D h j) with hfR
  have hcL : Continuous fL := by
    simp only [hfL, variance, tr]
    refine (Complex.continuous_re.comp ((cont_ps hcont).matrix_mul continuous_const).matrix_trace).sub
      ((Complex.continuous_re.comp ((cont_ps hcont).matrix_mul continuous_const).matrix_trace).pow 2)
  have hcR : Continuous fR := by
    simp only [hfR, weightedNormSq, weightedInner]
    refine continuous_finset_sum _ (fun j _ => continuous_const.mul ?_)
    exact Complex.continuous_re.comp (((cont_ps hcont).matrix_mul
      (cont_eff hcont h).matrix_conjTranspose).matrix_mul (cont_eff hcont h)).matrix_trace
  have hL : Filter.Tendsto fL (nhdsWithin 0 (Set.Ioi 0)) (nhds (fL 0)) :=
    (hcL.tendsto 0).mono_left nhdsWithin_le_nhds
  have hR : Filter.Tendsto fR (nhdsWithin 0 (Set.Ioi 0)) (nhds (fR 0)) :=
    (hcR.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), fL δ ≤ fR δ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    exact hpd_case (τδ δ) (hgood δ hδ).1 (hgood δ hδ).2
  have := le_of_tendsto_of_tendsto hL hR hev
  simpa only [hfL, hfR, h0] using this

end existence

end OTDHoeff

open OptimalTraceDistance.Estimation OTDHoeff in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Matrix ι ι ℂ) (hτ : τ.PosSemidef) (htr : τ.trace = 1)
    (n D : ℕ) (hn : 0 < n) (hD : D ≤ n)
    (h : (k : ℕ) → Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hherm : ∀ k ∈ Finset.Icc 1 D, (h k).IsHermitian)
    (hsym : ∀ k ∈ Finset.Icc 1 D, ∀ π : Equiv.Perm (Fin k),
      permutationOp π * h k * (permutationOp π)ᴴ = h k)
    (f₀ : ℝ) :
    variance τ n ((f₀ : ℂ) • 1 + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)) ≤
      ∑ j ∈ Finset.Icc 1 D, ((Nat.choose n j : ℝ))⁻¹ *
        weightedNormSq τ j (effectiveKernelGen τ D h j) :=
  variance_le_effectiveG hτ htr hn hD h hherm hsym f₀
