-- Prove2me | solution 1 for SetLike.GradedMonoid.eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/550ee9ee-2cc5-558b-8bac-b86785d4799c

import Mathlib
import Theorems.Thm_SetLike_GradedMonoid_listProd_ne_zero_of_linearIndependent_of_kunneth_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SetLike_GradedMonoid_eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective

set_option autoImplicit false

universe u

open TensorProduct DirectSum

namespace PB2

variable {k : Type u} [Field k] {H : Type u} {H' : Type u} [Ring H] [Algebra k H] [Ring H'] [Algebra k H']

def cntT {n : ℕ} (c : Fin n → Bool) : ℕ := ∑ i, if c i = true then 1 else 0

def cntF {n : ℕ} (c : Fin n → Bool) : ℕ := ∑ i, if c i = false then 1 else 0

theorem cntT_add_cntF {n : ℕ} (c : Fin n → Bool) : cntT c + cntF c = n := by
  unfold cntT cntF
  rw [← Finset.sum_add_distrib]
  have : ∀ i : Fin n, ((if c i = true then 1 else 0) + (if c i = false then 1 else 0) : ℕ) = 1 := by
    intro i; cases c i <;> simp
  simp [this]

theorem cntT_cons {n : ℕ} (b : Bool) (c : Fin n → Bool) :
    cntT (Fin.cons b c : Fin (n + 1) → Bool) = (if b = true then 1 else 0) + cntT c := by
  unfold cntT
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem cntF_cons {n : ℕ} (b : Bool) (c : Fin n → Bool) :
    cntF (Fin.cons b c : Fin (n + 1) → Bool) = (if b = false then 1 else 0) + cntF c := by
  unfold cntF
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

def sgn : (n : ℕ) → (Fin n → Bool) → ℤ
  | 0, _ => 1
  | n + 1, c => (if c 0 = true then 1 else (-1) ^ cntT (Fin.tail c)) * sgn n (Fin.tail c)

theorem sgn_cons {n : ℕ} (b : Bool) (c : Fin n → Bool) :
    sgn (n + 1) (Fin.cons b c) = (if b = true then 1 else (-1) ^ cntT c) * sgn n c := by
  simp only [sgn, Fin.cons_zero, Fin.tail_cons]

theorem sgn_eq_one_or {n : ℕ} (c : Fin n → Bool) : sgn n c = 1 ∨ sgn n c = -1 := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    have hc : c = Fin.cons (c 0) (Fin.tail c) := (Fin.cons_self_tail c).symm
    rw [hc, sgn_cons]
    rcases ih (Fin.tail c) with h | h
    · rw [h, mul_one]
      by_cases h0 : c 0 = true
      · left; rw [if_pos h0]
      · rw [if_neg h0]; exact neg_one_pow_eq_or ℤ _
    · rw [h, mul_neg, mul_one]
      by_cases h0 : c 0 = true
      · right; rw [if_pos h0]
      · rw [if_neg h0]
        rcases neg_one_pow_eq_or ℤ (cntT (Fin.tail c)) with h' | h' <;> rw [h'] <;> simp

theorem cast_sgn_ne_zero {n : ℕ} (c : Fin n → Bool) : ((sgn n c : ℤ) : k) ≠ 0 := by
  rcases sgn_eq_one_or c with h | h <;> rw [h] <;> simp

def sel {M : Type*} [Monoid M] {n : ℕ} (a : Fin n → M) (c : Fin n → Bool) (b : Bool) : M :=
  (List.ofFn fun i => if c i = b then a i else 1).prod

theorem sel_zero {M : Type*} [Monoid M] (a : Fin 0 → M) (c : Fin 0 → Bool) (b : Bool) : sel a c b = 1 := by
  simp [sel]

theorem sel_cons {M : Type*} [Monoid M] {n : ℕ} (a : Fin (n + 1) → M) (b₀ : Bool) (c : Fin n → Bool)
    (b : Bool) :
    sel a (Fin.cons b₀ c) b = (if b₀ = b then a 0 else 1) * sel (Fin.tail a) c b := by
  unfold sel
  rw [List.ofFn_succ, List.prod_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

theorem map_sel {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [FunLike F M N] [MonoidHomClass F M N]
    (φ : F) {n : ℕ} (a : Fin n → M) (c : Fin n → Bool) (b : Bool) :
    φ (sel a c b) = sel (fun i => φ (a i)) c b := by
  unfold sel
  rw [map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  simp only [Function.comp_apply]
  split_ifs <;> simp

theorem sel_true_mem (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] {n : ℕ} (x : Fin n → H)
    (hx : ∀ i, x i ∈ 𝒜 1) (c : Fin n → Bool) : sel x c true ∈ 𝒜 (cntT c) := by
  have h := SetLike.list_prod_ofFn_mem_graded (A := 𝒜) (fun i => if c i = true then 1 else 0)
    (fun i => if c i = true then x i else 1) (fun j => by
      by_cases hj : c j = true
      · simp only [hj, if_true]; exact hx j
      · simp only [hj]; exact SetLike.one_mem_graded 𝒜)
  rw [List.sum_ofFn] at h
  exact h

theorem sel_false_mem (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] {n : ℕ} (x : Fin n → H)
    (hx : ∀ i, x i ∈ 𝒜 1) (c : Fin n → Bool) : sel x c false ∈ 𝒜 (cntF c) := by
  have h := SetLike.list_prod_ofFn_mem_graded (A := 𝒜) (fun i => if c i = false then 1 else 0)
    (fun i => if c i = false then x i else 1) (fun j => by
      by_cases hj : c j = false
      · simp only [hj, if_true]; exact hx j
      · simp only [hj]; exact SetLike.one_mem_graded 𝒜)
  rw [List.sum_ofFn] at h
  exact h

theorem swap_sel {n : ℕ} (a : Fin n → H') (c : Fin n → Bool) (y : H') (hya : ∀ i, y * a i = -(a i * y)) :
    y * sel a c true = (-1) ^ cntT c * (sel a c true * y) := by
  induction n with
  | zero => simp [sel_zero, cntT]
  | succ n ih =>
    have hc : c = Fin.cons (c 0) (Fin.tail c) := (Fin.cons_self_tail c).symm
    rw [hc, sel_cons, cntT_cons]
    have ih' := ih (Fin.tail a) (Fin.tail c) (fun i => hya i.succ)
    by_cases h0 : c 0 = true
    · rw [if_pos h0, if_pos h0, ← mul_assoc, hya 0, neg_mul, mul_assoc, ih', pow_add, pow_one]
      simp only [neg_mul, one_mul, mul_assoc]
      congr 1
      rw [← mul_assoc, ← ((Commute.neg_one_left (a 0)).pow_left _).eq, mul_assoc]
    · rw [if_neg h0, if_neg h0, one_mul, zero_add, ih']

theorem expansion (p₁ p₂ : H →ₐ[k] H') {n : ℕ} (x : Fin n → H)
    (hanti : ∀ i j, p₂ (x i) * p₁ (x j) = -(p₁ (x j) * p₂ (x i))) :
    (List.ofFn fun i => p₁ (x i) + p₂ (x i)).prod =
      ∑ c : Fin n → Bool, (sgn n c : H') * (sel (fun i => p₁ (x i)) c true * sel (fun i => p₂ (x i)) c false) := by
  induction n with
  | zero =>
    simp [sel_zero, sgn]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have ih' := ih (Fin.tail x) (fun i j => hanti i.succ j.succ)
    have htail : (List.ofFn fun i : Fin n => p₁ (x i.succ) + p₂ (x i.succ)) =
        (List.ofFn fun i : Fin n => p₁ (Fin.tail x i) + p₂ (Fin.tail x i)) := rfl
    rw [htail, ih', Finset.mul_sum]

    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    rw [sgn_cons, sgn_cons, sel_cons, sel_cons, sel_cons, sel_cons]
    have htl₁ : Fin.tail (fun i => p₁ (x i)) = fun i => p₁ (Fin.tail x i) := rfl
    have htl₂ : Fin.tail (fun i => p₂ (x i)) = fun i => p₂ (Fin.tail x i) := rfl
    rw [htl₁, htl₂]
    set A := sel (fun i => p₁ (Fin.tail x i)) c true
    set B := sel (fun i => p₂ (Fin.tail x i)) c false
    set σ : H' := ((sgn n c : ℤ) : H')
    have hsw : p₂ (x 0) * A = (-1) ^ cntT c * (A * p₂ (x 0)) :=
      swap_sel (fun i => p₁ (Fin.tail x i)) c (p₂ (x 0)) (fun i => hanti 0 i.succ)
    have hi : p₁ (x 0) * (σ * (A * B)) = σ * (p₁ (x 0) * A * B) := by
      rw [← mul_assoc, ← (Int.cast_commute (sgn n c) (p₁ (x 0))).eq]
      simp only [σ, mul_assoc]
    have hii : p₂ (x 0) * (σ * (A * B)) = (-1) ^ cntT c * σ * (A * (p₂ (x 0) * B)) := by
      rw [← mul_assoc, ← (Int.cast_commute (sgn n c) (p₂ (x 0))).eq, mul_assoc, ← mul_assoc (p₂ (x 0)),
        hsw]
      simp only [σ, mul_assoc]
      rw [← mul_assoc, ← ((Commute.neg_one_left _).pow_left _).eq, mul_assoc]
    rw [add_mul, hi, hii]
    simp only [σ, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true, one_mul, mul_assoc, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one]

def δ {n : ℕ} (j : Fin n) : Fin n → Bool := fun i => decide (i ≠ j)

theorem δ_apply_eq_false {n : ℕ} (j i : Fin n) : δ j i = false ↔ i = j := by
  simp [δ]

theorem δ_injective {n : ℕ} : Function.Injective (δ : Fin n → Fin n → Bool) := by
  intro j j' h
  have h1 : δ j' j = false := by rw [← h]; simp [δ]
  exact (δ_apply_eq_false j' j).1 h1

theorem cntF_δ {n : ℕ} (j : Fin n) : cntF (δ j) = 1 := by
  unfold cntF
  rw [Finset.sum_boole]
  simp [δ_apply_eq_false, Finset.filter_eq']

theorem cntT_δ {n : ℕ} (j : Fin (n + 1)) : cntT (δ j) = n := by
  have h := cntT_add_cntF (δ j)
  rw [cntF_δ] at h
  omega

theorem eq_δ_of_cntF_eq_one {n : ℕ} (c : Fin n → Bool) (h : cntF c = 1) : ∃ j, c = δ j := by
  unfold cntF at h
  rw [Finset.sum_boole, Nat.cast_id, Finset.card_eq_one] at h
  obtain ⟨j, hj⟩ := h
  refine ⟨j, funext fun i => ?_⟩
  have hi : (c i = false) ↔ i = j := by
    have := Finset.ext_iff.1 hj i
    simpa using this
  by_cases hij : i = j
  · rw [hi.2 hij, eq_comm, δ_apply_eq_false]; exact hij
  · have h1 : c i = true := by
      cases h' : c i
      · exact absurd (hi.1 h') hij
      · rfl
    rw [h1, eq_comm]
    simpa [δ] using hij

theorem sel_single {M : Type*} [Monoid M] {n : ℕ} (a : Fin n → M) (j : Fin n) :
    (List.ofFn fun i => if i = j then a i else 1).prod = a j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun j' => ?_) j
    · rw [if_pos rfl]
      have : (List.ofFn fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then a i.succ else 1) =
          List.ofFn fun _ : Fin n => (1 : M) := by
        refine congrArg List.ofFn (funext fun i => ?_)
        rw [if_neg (Fin.succ_ne_zero i)]
      rw [this]
      have h1 : (List.ofFn fun _ : Fin n => (1 : M)).prod = 1 := by
        rw [List.ofFn_const, List.prod_replicate, one_pow]
      rw [h1, mul_one]
    · rw [if_neg (Fin.succ_ne_zero j').symm]
      rw [one_mul]
      have : (List.ofFn fun i : Fin n => if i.succ = j'.succ then a i.succ else 1) =
          List.ofFn fun i : Fin n => if i = j' then (Fin.tail a) i else 1 := by
        refine congrArg List.ofFn (funext fun i => ?_)
        simp only [Fin.succ_inj]
        rfl
      rw [this, ih (Fin.tail a) j']
      rfl

theorem sel_δ_false {M : Type*} [Monoid M] {n : ℕ} (a : Fin n → M) (j : Fin n) : sel a (δ j) false = a j := by
  unfold sel
  have : (fun i => if δ j i = false then a i else 1) = fun i => if i = j then a i else 1 := by
    funext i
    by_cases h : i = j
    · rw [if_pos h, if_pos ((δ_apply_eq_false j i).2 h)]
    · rw [if_neg h, if_neg (mt (δ_apply_eq_false j i).1 h)]
  rw [this, sel_single]

theorem sel_δ_zero_true {M : Type*} [Monoid M] {n : ℕ} (a : Fin (n + 1) → M) :
    sel a (δ 0) true = (List.ofFn (Fin.tail a)).prod := by
  unfold sel
  rw [List.ofFn_succ, List.prod_cons]
  have h0 : (if δ (0 : Fin (n + 1)) 0 = true then a 0 else 1) = 1 := by
    rw [if_neg]; simp [δ]
  rw [h0, one_mul]
  congr 1

theorem sel_δ_true_mem (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] {n : ℕ} (x : Fin (n + 1) → H)
    (hx : ∀ i, x i ∈ 𝒜 1) (j : Fin (n + 1)) : sel x (δ j) true ∈ 𝒜 n := by
  have h := sel_true_mem 𝒜 x hx (δ j)
  rwa [cntT_δ] at h

theorem eq_zero_of_sum_smul_tmul_eq_zero {ι : Type*} [Fintype ι] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (X : ι → V) (hX : LinearIndependent k X) (Y : ι → W) (ε : ι → k)
    (hε : ∀ i, ε i ≠ 0) (h : ∑ i, ε i • (Y i ⊗ₜ[k] X i) = 0) (j : ι) : Y j = 0 := by
  classical

  have hinj : Function.Injective X := hX.injective
  set s : Set V := Set.range X
  have hs : LinearIndepOn k id s := hX.linearIndepOn_id
  let b := Module.Basis.extend hs
  have hmem : ∀ i, X i ∈ hs.extend (Set.subset_univ s) := fun i =>
    Module.Basis.subset_extend hs (Set.mem_range_self i)
  let φ : V →ₗ[k] k := b.coord ⟨X j, hmem j⟩
  have hφ : ∀ i, φ (X i) = if i = j then 1 else 0 := by
    intro i
    have hb : b ⟨X i, hmem i⟩ = X i := Module.Basis.extend_apply_self hs _
    show b.repr (X i) ⟨X j, hmem j⟩ = _
    rw [← hb, b.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg, if_neg hij]
      intro h'
      exact hij (hinj (Subtype.ext_iff.1 h'))

  have h2 := congrArg (fun t => TensorProduct.rid k W (LinearMap.lTensor W φ t)) h
  simp only [map_sum, map_smul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero] at h2
  simp only [hφ, ite_smul, one_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h2
  exact (smul_eq_zero.1 h2).resolve_left (hε j)

abbrev kunnethMap (𝒜 : ℕ → Submodule k H) (p₁ p₂ : H →ₐ[k] H') (p : ℕ × ℕ) :
    ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2) →ₗ[k] H' :=
  LinearMap.mul' k H' ∘ₗ TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 p.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 p.2).subtype)

theorem main (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] [Nontrivial H]
    (p₁ p₂ m : H →ₐ[k] H')
    (hanti : ∀ a ∈ 𝒜 1, ∀ b ∈ 𝒜 1, p₂ a * p₁ b = -(p₁ b * p₂ a))
    (hm : ∀ a ∈ 𝒜 1, m a = p₁ a + p₂ a)
    (hK : Function.Injective
      (DirectSum.toModule k (ℕ × ℕ) H' fun p => kunnethMap 𝒜 p₁ p₂ p)) :
    ∀ (n : ℕ) (x : Fin n → H), (∀ i, x i ∈ 𝒜 1) → LinearIndependent k x → (List.ofFn x).prod ≠ 0 := by
  classical
  intro n
  induction n with
  | zero =>
    intro x _ _
    rw [List.ofFn_zero, List.prod_nil]
    exact one_ne_zero
  | succ n ih =>
    intro x hx hli heq

    have h1 : (List.ofFn fun i => p₁ (x i) + p₂ (x i)).prod = 0 := by
      have : m (List.ofFn x).prod = (List.ofFn fun i => p₁ (x i) + p₂ (x i)).prod := by
        rw [map_list_prod, List.map_ofFn]
        congr 1
        exact congrArg List.ofFn (funext fun i => hm _ (hx i))
      rw [← this, heq, map_zero]
    rw [expansion p₁ p₂ x (fun i j => hanti _ (hx i) _ (hx j))] at h1

    let idx : (Fin (n + 1) → Bool) → ℕ × ℕ := fun c => (cntT c, cntF c)
    let e : (c : Fin (n + 1) → Bool) → ↥(𝒜 (idx c).1) ⊗[k] ↥(𝒜 (idx c).2) := fun c =>
      ((sgn (n + 1) c : ℤ) : k) •
        ((⟨sel x c true, sel_true_mem 𝒜 x hx c⟩ : ↥(𝒜 (cntT c))) ⊗ₜ[k]
          (⟨sel x c false, sel_false_mem 𝒜 x hx c⟩ : ↥(𝒜 (cntF c))))
    let U : ⨁ p : ℕ × ℕ, ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2) :=
      ∑ c, DirectSum.lof k (ℕ × ℕ) (fun p => ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2)) (idx c) (e c)
    have hU : DirectSum.toModule k (ℕ × ℕ) H' (fun p => kunnethMap 𝒜 p₁ p₂ p) U = 0 := by
      rw [← h1]
      simp only [U, map_sum, DirectSum.toModule_lof]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [e, map_smul, kunnethMap, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, Submodule.subtype_apply]
      rw [map_sel p₁, map_sel p₂, Algebra.smul_def, map_intCast]
    have hU0 : U = 0 := hK (by rw [hU, map_zero])

    have hcomp : U (n, 1) = ∑ j : Fin (n + 1),
        ((sgn (n + 1) (δ j) : ℤ) : k) •
          ((⟨sel x (δ j) true, sel_δ_true_mem 𝒜 x hx j⟩ : ↥(𝒜 n)) ⊗ₜ[k]
            (⟨x j, hx j⟩ : ↥(𝒜 1))) := by
      simp only [U, DirectSum.sum_apply]

      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => idx c = (n, 1))]
      have hzero : ∑ c ∈ Finset.univ.filter (fun c => ¬ idx c = (n, 1)),
          (DirectSum.lof k (ℕ × ℕ) (fun p => ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2)) (idx c) (e c)) (n, 1) = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        rw [Finset.mem_filter] at hc
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
        exact fun h => hc.2 h.symm
      rw [hzero, add_zero]

      have hfilter : Finset.univ.filter (fun c : Fin (n + 1) → Bool => idx c = (n, 1)) =
          Finset.univ.image δ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hc
          obtain ⟨j, rfl⟩ := eq_δ_of_cntF_eq_one c (congrArg Prod.snd hc)
          exact ⟨j, rfl⟩
        · rintro ⟨j, rfl⟩
          exact Prod.ext (cntT_δ j) (cntF_δ j)
      rw [hfilter, Finset.sum_image (fun j _ j' _ h => δ_injective h)]
      refine Finset.sum_congr rfl fun j _ => ?_

      have hidx : idx (δ j) = (n, 1) := Prod.ext (cntT_δ j) (cntF_δ j)
      have key : ∀ (q : ℕ × ℕ) (hq : q = (n, 1)) (v w : H) (hv : v ∈ 𝒜 q.1) (hw : w ∈ 𝒜 q.2)
          (hv' : v ∈ 𝒜 n) (hw' : w ∈ 𝒜 1) (s : k),
          (DirectSum.lof k (ℕ × ℕ) (fun p => ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2)) q
            (s • ((⟨v, hv⟩ : ↥(𝒜 q.1)) ⊗ₜ[k] (⟨w, hw⟩ : ↥(𝒜 q.2))))) (n, 1) =
            s • ((⟨v, hv'⟩ : ↥(𝒜 n)) ⊗ₜ[k] (⟨w, hw'⟩ : ↥(𝒜 1))) := by
        intro q hq v w hv hw hv' hw' s
        subst hq
        rw [DirectSum.lof_apply]
      have hwj : sel x (δ j) false ∈ 𝒜 1 := by
        have h := sel_false_mem 𝒜 x hx (δ j)
        rwa [cntF_δ] at h
      have := key (idx (δ j)) hidx (sel x (δ j) true) (sel x (δ j) false) (sel_true_mem 𝒜 x hx _)
        (sel_false_mem 𝒜 x hx _) (sel_δ_true_mem 𝒜 x hx j) hwj ((sgn (n + 1) (δ j) : ℤ) : k)
      rw [this]
      congr 2
      exact Subtype.ext (sel_δ_false x j)
    rw [hU0, DirectSum.zero_apply] at hcomp

    have hli' : LinearIndependent k (fun j : Fin (n + 1) => (⟨x j, hx j⟩ : ↥(𝒜 1))) :=
      LinearIndependent.of_comp (𝒜 1).subtype (by exact hli)
    have hY := eq_zero_of_sum_smul_tmul_eq_zero (fun j : Fin (n + 1) => (⟨x j, hx j⟩ : ↥(𝒜 1))) hli'
      (fun j => (⟨sel x (δ j) true, sel_δ_true_mem 𝒜 x hx j⟩ : ↥(𝒜 n)))
      (fun j => ((sgn (n + 1) (δ j) : ℤ) : k)) (fun j => cast_sgn_ne_zero (δ j)) hcomp.symm 0
    have hY' : sel x (δ 0) true = 0 := congrArg Subtype.val hY
    rw [sel_δ_zero_true] at hY'

    exact ih (Fin.tail x) (fun i => hx i.succ) (hli.comp Fin.succ (Fin.succ_injective n)) hY'

theorem comm_sel {n : ℕ} (a : Fin n → H') (c : Fin n → Bool) (y : H') (hya : ∀ i, y * a i = a i * y) (b : Bool) :
    y * sel a c b = sel a c b * y := by
  induction n with
  | zero => rw [sel_zero, mul_one, one_mul]
  | succ n ih =>
    have hc : c = Fin.cons (c 0) (Fin.tail c) := by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
    rw [hc, sel_cons]
    have ih' := ih (Fin.tail a) (Fin.tail c) (fun i => hya i.succ)
    split_ifs with h0
    · rw [← mul_assoc, hya 0, mul_assoc, ih', mul_assoc]
    · rw [one_mul, ih']

theorem expansion2 (p₁ p₂ : H →ₐ[k] H') {n : ℕ} (a : Fin n → H) (x : H)
    (hanti : ∀ i j, p₂ (a i) * p₁ (a j) = -(p₁ (a j) * p₂ (a i)))
    (hcomm : ∀ i, p₂ x * p₁ (a i) = p₁ (a i) * p₂ x) :
    (p₁ x + p₂ x) * (List.ofFn fun i => p₁ (a i) + p₂ (a i)).prod =
      ∑ c : Fin n → Bool, (sgn n c : H') *
        (p₁ (x * sel a c true) * p₂ (sel a c false) + p₁ (sel a c true) * p₂ (x * sel a c false)) := by
  rw [expansion p₁ p₂ a hanti, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_mul, map_sel p₁, map_sel p₂, add_mul, mul_add]
  congr 1
  · rw [← mul_assoc, ← (Int.cast_commute (sgn n c) (p₁ x)).eq, mul_assoc, mul_assoc]
  · rw [← mul_assoc, ← (Int.cast_commute (sgn n c) (p₂ x)).eq, mul_assoc, ← mul_assoc (p₂ x),
      comm_sel (fun i => p₁ (a i)) c (p₂ x) hcomm true, mul_assoc]

theorem eq_false_of_cntT_eq_zero {n : ℕ} (c : Fin n → Bool) (h : cntT c = 0) : c = fun _ => false := by
  funext i
  unfold cntT at h
  have := (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
  cases hci : c i
  · rfl
  · rw [hci, if_pos rfl] at this
    exact absurd this one_ne_zero

end PB2

namespace PB2

variable {k : Type u} [Field k] {H : Type u} {H' : Type u} [Ring H] [Algebra k H] [Ring H'] [Algebra k H']

theorem sel_allFalse_true {M : Type*} [Monoid M] {n : ℕ} (a : Fin n → M) : sel a (fun _ => false) true = 1 := by
  unfold sel; simp

theorem sel_allFalse_false {M : Type*} [Monoid M] {n : ℕ} (a : Fin n → M) : sel a (fun _ => false) false = (List.ofFn a).prod := by
  unfold sel; simp

theorem cntF_allFalse (n : ℕ) : cntF (fun _ : Fin n => false) = n := by
  unfold cntF; simp

def τ {n : ℕ} (i j : Fin n) : Fin n → Bool := fun l => decide (l = i ∨ l = j)

theorem cntT_eq_card {n : ℕ} (c : Fin n → Bool) : cntT c = (Finset.univ.filter fun l => c l = true).card := by
  unfold cntT
  rw [Finset.card_filter]

theorem cntT_τ {n : ℕ} {i j : Fin n} (hij : i < j) : cntT (τ i j) = 2 := by
  rw [cntT_eq_card]
  have : (Finset.univ.filter fun l => τ i j l = true) = {i, j} := by
    ext l; simp [τ]
  rw [this, Finset.card_pair (ne_of_lt hij)]

theorem exists_τ_of_cntT_eq_two {n : ℕ} (c : Fin n → Bool) (h : cntT c = 2) : ∃ i j : Fin n, i < j ∧ c = τ i j := by
  classical
  rw [cntT_eq_card, Finset.card_eq_two] at h
  obtain ⟨i, j, hne, hS⟩ := h
  have key : ∀ l, c l = true ↔ l = i ∨ l = j := fun l => by
    have := congrArg (l ∈ ·) hS
    simpa using this
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨i, j, hlt, funext fun l => by
      have := key l; unfold τ; rcases Bool.eq_false_or_eq_true (c l) with h1 | h1 <;> simp_all⟩
  · exact ⟨j, i, hgt, funext fun l => by
      have := key l; unfold τ; rcases Bool.eq_false_or_eq_true (c l) with h1 | h1 <;> simp_all [or_comm]⟩

theorem τ_injective {n : ℕ} {i j i' j' : Fin n} (hij : i < j) (hij' : i' < j') (h : τ i j = τ i' j') : i = i' ∧ j = j' := by
  have hi : τ i' j' i = true := by rw [← h]; simp [τ]
  have hj : τ i' j' j = true := by rw [← h]; simp [τ]
  simp only [τ, decide_eq_true_eq] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with h2 | h2
  · exact absurd hij (by rw [h2]; exact lt_irrefl _)
  · exact ⟨rfl, h2⟩
  · subst h2; exact absurd (hij.trans hij') (lt_irrefl _)
  · subst h2; exact absurd hij (lt_irrefl _)

end PB2

namespace PB2

theorem sel_τ_true {M : Type*} [Monoid M] {n : ℕ} (a : Fin n → M) {i j : Fin n} (hij : i < j) :
    sel a (τ i j) true = a i * a j := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    unfold sel
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hi0 : i = 0
    · subst hi0
      have hj0 : j ≠ 0 := ne_of_gt hij
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
      have h0 : (if τ (0 : Fin (n + 1)) j'.succ 0 = true then a 0 else 1) = a 0 := by rw [if_pos]; simp [τ]
      rw [h0]
      congr 1
      have : (List.ofFn fun l : Fin n => if τ (0 : Fin (n + 1)) j'.succ l.succ = true then a l.succ else 1) =
          List.ofFn fun l : Fin n => if l = j' then (Fin.tail a) l else 1 := by
        refine congrArg List.ofFn (funext fun l => ?_)
        have : (τ (0 : Fin (n + 1)) j'.succ l.succ = true) ↔ l = j' := by simp [τ, Fin.succ_ne_zero, Fin.succ_inj]
        by_cases h : l = j'
        · rw [if_pos (this.mpr h), if_pos h]; rfl
        · rw [if_neg (mt this.mp h), if_neg h]
      rw [this, sel_single]
      rfl
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
      have hj0 : j ≠ 0 := fun h => by rw [h] at hij; exact absurd hij (Fin.not_lt_zero _)
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj0
      have h0 : (if τ i'.succ j'.succ (0 : Fin (n + 1)) = true then a 0 else 1) = 1 := by
        rw [if_neg]; simp [τ, (Fin.succ_ne_zero i').symm, (Fin.succ_ne_zero j').symm]
      rw [h0, one_mul]
      have : (List.ofFn fun l : Fin n => if τ i'.succ j'.succ l.succ = true then a l.succ else 1) =
          List.ofFn fun l : Fin n => if τ i' j' l = true then (Fin.tail a) l else 1 := by
        refine congrArg List.ofFn (funext fun l => ?_)
        have : (τ i'.succ j'.succ l.succ = true) ↔ (τ i' j' l = true) := by simp [τ, Fin.succ_inj]
        by_cases h : τ i' j' l = true
        · rw [if_pos (this.mpr h), if_pos h]; rfl
        · rw [if_neg (mt this.mp h), if_neg h]
      rw [this]
      have ih' := ih (Fin.tail a) (Fin.succ_lt_succ_iff.mp hij)
      unfold sel at ih'
      rw [ih']
      rfl

end PB2

namespace PB2

variable {k : Type u} [Field k]

theorem exists_dual_family {ι : Type*} [DecidableEq ι] {V : Type*} [AddCommGroup V] [Module k V] (X : ι → V) (hX : LinearIndependent k X) :
    ∃ ψ : ι → (V →ₗ[k] k), ∀ i j, ψ j (X i) = if i = j then 1 else 0 := by
  classical
  have hinj : Function.Injective X := hX.injective
  set s : Set V := Set.range X
  have hs : LinearIndepOn k id s := hX.linearIndepOn_id
  let b := Module.Basis.extend hs
  have hmem : ∀ i, X i ∈ hs.extend (Set.subset_univ s) := fun i =>
    Module.Basis.subset_extend hs (Set.mem_range_self i)
  refine ⟨fun j => b.coord ⟨X j, hmem j⟩, fun i j => ?_⟩
  have hb : b ⟨X i, hmem i⟩ = X i := Module.Basis.extend_apply_self hs _
  show b.repr (X i) ⟨X j, hmem j⟩ = _
  rw [← hb, b.repr_self, Finsupp.single_apply]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg, if_neg hij]
    intro h'
    exact hij (hinj (Subtype.ext_iff.1 h'))

theorem exists_dual_eq_one {V : Type*} [AddCommGroup V] [Module k V] (v : V) (hv : v ≠ 0) :
    ∃ φ : V →ₗ[k] k, φ v = 1 := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_dual_family (fun _ : Unit => v) ((linearIndependent_unique_iff (R := k) (v := fun _ : Unit => v)).mpr hv)
  exact ⟨ψ (), by simpa using hψ () ()⟩

end PB2

open scoped TensorProduct DirectSum

open PB2 in
theorem solution
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hcomm : ∀ x ∈ 𝒜 2, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = p₁ y * p₂ x)
    (hm : ∀ y ∈ 𝒜 1, m y = p₁ y + p₂ y)
    {d : ℕ} (a : Fin d → H) (ha : ∀ i, a i ∈ 𝒜 1) (hli : LinearIndependent k a)
    (hd : ∀ n : ℕ, d < n → 𝒜 n = ⊥)
    (x : H) (hx : x ∈ 𝒜 2) (hmx : m x = p₁ x + p₂ x) :
    x = 0 := by
  classical
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact Subsingleton.elim _ _
  by_cases hd1 : d ≤ 1
  · have h2 := hd 2 (by omega)
    rw [h2, Submodule.mem_bot] at hx
    exact hx
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩

  let a' : Fin n → H := fun i => a (Fin.castSucc i)
  have ha' : ∀ i, a' i ∈ 𝒜 1 := fun i => ha _
  have hli' : LinearIndependent k a' := hli.comp Fin.castSucc (Fin.castSucc_injective n)
  have hprod_mem : (List.ofFn a').prod ∈ 𝒜 n := by
    have h1 := SetLike.list_prod_ofFn_mem_graded (A := 𝒜) (fun _ : Fin n => (1 : ℕ)) a' (fun i => ha' i)
    rwa [List.ofFn_const, List.sum_replicate, smul_eq_mul, mul_one] at h1
  have hP : (List.ofFn a').prod ≠ 0 :=
    SetLike.GradedMonoid.listProd_ne_zero_of_linearIndependent_of_kunneth_injective 𝒜 p₁ p₂ m hK hanti hm a' ha' hli'

  have hy : x * (List.ofFn a').prod = 0 := by
    have hmem : x * (List.ofFn a').prod ∈ 𝒜 (2 + n) := SetLike.mul_mem_graded hx hprod_mem
    have := hd (2 + n) (by omega)
    rw [this, Submodule.mem_bot] at hmem
    exact hmem

  have h1 : ∑ c : Fin n → Bool, (sgn n c : H') *
      (p₁ (x * sel a' c true) * p₂ (sel a' c false) + p₁ (sel a' c true) * p₂ (x * sel a' c false)) = 0 := by
    rw [← expansion2 p₁ p₂ a' x (fun i j => hanti _ (ha' i) _ (ha' j)) (fun i => hcomm _ hx _ (ha' i)), ← hmx]
    have : m (x * (List.ofFn a').prod) = m x * (List.ofFn fun i => p₁ (a' i) + p₂ (a' i)).prod := by
      rw [map_mul, map_list_prod, List.map_ofFn]
      congr 2
      exact congrArg List.ofFn (funext fun i => hm _ (ha' i))
    rw [← this, hy, map_zero]

  let idx₁ : (Fin n → Bool) → ℕ × ℕ := fun c => (2 + cntT c, cntF c)
  let idx₂ : (Fin n → Bool) → ℕ × ℕ := fun c => (cntT c, 2 + cntF c)
  let e₁ : (c : Fin n → Bool) → ↥(𝒜 (idx₁ c).1) ⊗[k] ↥(𝒜 (idx₁ c).2) := fun c =>
    ((sgn n c : ℤ) : k) •
      ((⟨x * sel a' c true, SetLike.mul_mem_graded hx (sel_true_mem 𝒜 a' ha' c)⟩ : ↥(𝒜 (2 + cntT c))) ⊗ₜ[k]
        (⟨sel a' c false, sel_false_mem 𝒜 a' ha' c⟩ : ↥(𝒜 (cntF c))))
  let e₂ : (c : Fin n → Bool) → ↥(𝒜 (idx₂ c).1) ⊗[k] ↥(𝒜 (idx₂ c).2) := fun c =>
    ((sgn n c : ℤ) : k) •
      ((⟨sel a' c true, sel_true_mem 𝒜 a' ha' c⟩ : ↥(𝒜 (cntT c))) ⊗ₜ[k]
        (⟨x * sel a' c false, SetLike.mul_mem_graded hx (sel_false_mem 𝒜 a' ha' c)⟩ : ↥(𝒜 (2 + cntF c))))
  let U : ⨁ p : ℕ × ℕ, ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2) :=
    ∑ c, (DirectSum.lof k (ℕ × ℕ) (fun p => ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2)) (idx₁ c) (e₁ c) +
      DirectSum.lof k (ℕ × ℕ) (fun p => ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2)) (idx₂ c) (e₂ c))
  have hU : DirectSum.toModule k (ℕ × ℕ) H' (fun p => kunnethMap 𝒜 p₁ p₂ p) U = 0 := by
    rw [← h1]
    simp only [U, map_sum, map_add, DirectSum.toModule_lof]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [e₁, e₂, map_smul, kunnethMap, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AlgHom.toLinearMap_apply, Submodule.subtype_apply]
    rw [← smul_add, Algebra.smul_def, map_intCast]
  have hU0 : U = 0 := hK (by rw [hU, map_zero])

  have key : ∀ (q : ℕ × ℕ) (q₀ : ℕ × ℕ) (hq : q = q₀) (v w : H) (hv : v ∈ 𝒜 q.1) (hw : w ∈ 𝒜 q.2)
      (hv' : v ∈ 𝒜 q₀.1) (hw' : w ∈ 𝒜 q₀.2) (s : k),
      (DirectSum.lof k (ℕ × ℕ) (fun p => ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2)) q
        (s • ((⟨v, hv⟩ : ↥(𝒜 q.1)) ⊗ₜ[k] (⟨w, hw⟩ : ↥(𝒜 q.2))))) q₀ =
        s • ((⟨v, hv'⟩ : ↥(𝒜 q₀.1)) ⊗ₜ[k] (⟨w, hw'⟩ : ↥(𝒜 q₀.2))) := by
    intro q q₀ hq v w hv hw hv' hw' s
    subst hq
    rw [DirectSum.lof_apply]

  let PT := {q : Fin n × Fin n // q.1 < q.2}
  have hmemn : ∀ q : PT, x * sel a' (τ q.1.1 q.1.2) false ∈ 𝒜 n := by
    intro q
    have h := SetLike.mul_mem_graded hx (sel_false_mem 𝒜 a' ha' (τ q.1.1 q.1.2))
    have hsum := cntT_add_cntF (τ q.1.1 q.1.2)
    rw [cntT_τ q.2] at hsum
    rwa [show 2 + cntF (τ q.1.1 q.1.2) = n by omega] at h
  have hidx₂ : ∀ q : PT, idx₂ (τ q.1.1 q.1.2) = (2, n) := by
    intro q
    have hsum := cntT_add_cntF (τ q.1.1 q.1.2)
    rw [cntT_τ q.2] at hsum
    exact Prod.ext (cntT_τ q.2) (by show 2 + cntF (τ q.1.1 q.1.2) = n; omega)
  have hcntT0 : cntT (fun _ : Fin n => false) = 0 := by unfold cntT; simp
  have hidx₁ : idx₁ (fun _ => false) = (2, n) := Prod.ext (by show 2 + cntT (fun _ : Fin n => false) = 2; rw [hcntT0]) (cntF_allFalse n)

  have hcomp : U (2, n) =
      ((sgn n (fun _ => false) : ℤ) : k) • ((⟨x, hx⟩ : ↥(𝒜 2)) ⊗ₜ[k] (⟨(List.ofFn a').prod, hprod_mem⟩ : ↥(𝒜 n))) +
      ∑ q : PT, ((sgn n (τ q.1.1 q.1.2) : ℤ) : k) •
        ((⟨a' q.1.1 * a' q.1.2, SetLike.mul_mem_graded (ha' q.1.1) (ha' q.1.2)⟩ : ↥(𝒜 2)) ⊗ₜ[k]
          (⟨x * sel a' (τ q.1.1 q.1.2) false, hmemn q⟩ : ↥(𝒜 n))) := by
    simp only [U]
    rw [DirectSum.apply_eq_component k, map_sum]
    simp only [map_add, ← DirectSum.apply_eq_component]
    rw [Finset.sum_add_distrib]
    congr 1
    ·
      rw [Finset.sum_eq_single (fun _ : Fin n => false)]
      · rw [key (idx₁ fun _ => false) (2, n) hidx₁ _ _ _ _ (by rw [sel_allFalse_true, mul_one]; exact hx)
          (by rw [sel_allFalse_false]; exact hprod_mem)]
        congr 2 <;> apply Subtype.ext <;> simp [sel_allFalse_true, sel_allFalse_false]
      · intro c _ hc
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
        intro h
        apply hc
        have h' : 2 = 2 + cntT c := congrArg Prod.fst h
        exact eq_false_of_cntT_eq_zero c (by omega)
      · intro h; exact absurd (Finset.mem_univ _) h
    ·
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => idx₂ c = (2, n))]
      have hzero : ∑ c ∈ Finset.univ.filter (fun c => ¬ idx₂ c = (2, n)),
          (DirectSum.lof k (ℕ × ℕ) (fun p => ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2)) (idx₂ c) (e₂ c)) (2, n) = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        rw [Finset.mem_filter] at hc
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
        exact fun h => hc.2 h.symm
      rw [hzero, add_zero]
      have hfilter : Finset.univ.filter (fun c : Fin n → Bool => idx₂ c = (2, n)) =
          Finset.univ.image (fun q : PT => τ q.1.1 q.1.2) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hc
          have h2 : cntT c = 2 := congrArg Prod.fst hc
          obtain ⟨i, j, hij, rfl⟩ := exists_τ_of_cntT_eq_two c h2
          exact ⟨⟨(i, j), hij⟩, rfl⟩
        · rintro ⟨q, rfl⟩
          exact hidx₂ q
      rw [hfilter, Finset.sum_image (fun q _ q' _ h => by
        have := τ_injective q.2 q'.2 h
        exact Subtype.ext (Prod.ext this.1 this.2))]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [key (idx₂ (τ q.1.1 q.1.2)) (2, n) (hidx₂ q) _ _ _ _
        (by rw [sel_τ_true a' q.2]; exact SetLike.mul_mem_graded (ha' q.1.1) (ha' q.1.2)) (hmemn q)]
      congr 2
      apply Subtype.ext
      exact sel_τ_true a' q.2
  rw [hU0, DirectSum.zero_apply] at hcomp

  have hPne : (⟨(List.ofFn a').prod, hprod_mem⟩ : ↥(𝒜 n)) ≠ 0 := fun h => hP (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ := exists_dual_eq_one (k := k) _ hPne
  have h2 := congrArg (fun t => TensorProduct.rid k ↥(𝒜 2) (LinearMap.lTensor ↥(𝒜 2) φ t)) hcomp
  simp only [map_add, map_sum, map_smul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero, hφ, one_smul] at h2

  set s₀ : k := ((sgn n (fun _ : Fin n => false) : ℤ) : k) with hs₀
  have hs₀ne : s₀ ≠ 0 := cast_sgn_ne_zero _
  let κ : PT → k := fun q => -(s₀⁻¹ * (((sgn n (τ q.1.1 q.1.2) : ℤ) : k) * φ ⟨x * sel a' (τ q.1.1 q.1.2) false, hmemn q⟩))
  have hX : (⟨x, hx⟩ : ↥(𝒜 2)) = ∑ q : PT, κ q • (⟨a' q.1.1 * a' q.1.2, SetLike.mul_mem_graded (ha' q.1.1) (ha' q.1.2)⟩ : ↥(𝒜 2)) := by
    have h3 : s₀ • (⟨x, hx⟩ : ↥(𝒜 2)) = -∑ q : PT, ((sgn n (τ q.1.1 q.1.2) : ℤ) : k) •
        (φ ⟨x * sel a' (τ q.1.1 q.1.2) false, hmemn q⟩ • (⟨a' q.1.1 * a' q.1.2, _⟩ : ↥(𝒜 2))) :=
      eq_neg_of_add_eq_zero_left h2.symm
    rw [← inv_smul_smul₀ hs₀ne (⟨x, hx⟩ : ↥(𝒜 2)), h3, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [κ, smul_smul]; rw [← neg_smul]
  have hxsum : x = ∑ q : PT, κ q • (a' q.1.1 * a' q.1.2) := by
    have := congrArg Subtype.val hX
    simpa [Submodule.coe_sum, Submodule.coe_smul] using this

  let D : ↥(𝒜 1) ⊗[k] ↥(𝒜 1) := ∑ q : PT, κ q •
    (((⟨a' q.1.1, ha' q.1.1⟩ : ↥(𝒜 1)) ⊗ₜ[k] (⟨a' q.1.2, ha' q.1.2⟩ : ↥(𝒜 1))) -
      ((⟨a' q.1.2, ha' q.1.2⟩ : ↥(𝒜 1)) ⊗ₜ[k] (⟨a' q.1.1, ha' q.1.1⟩ : ↥(𝒜 1))))
  have hD : DirectSum.toModule k (ℕ × ℕ) H' (fun p => kunnethMap 𝒜 p₁ p₂ p)
      (DirectSum.lof k (ℕ × ℕ) (fun p => ↥(𝒜 p.1) ⊗[k] ↥(𝒜 p.2)) (1, 1) D) = 0 := by
    rw [DirectSum.toModule_lof]
    have hcalc : kunnethMap 𝒜 p₁ p₂ (1, 1) D = ∑ q : PT, κ q • (p₁ (a' q.1.1) * p₂ (a' q.1.2) - p₁ (a' q.1.2) * p₂ (a' q.1.1)) := by
      simp only [D, map_sum, map_smul, map_sub, kunnethMap, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        AlgHom.toLinearMap_apply, Submodule.subtype_apply]
    rw [hcalc]
    have hm2 : m x - p₁ x - p₂ x = ∑ q : PT, κ q • (p₁ (a' q.1.1) * p₂ (a' q.1.2) - p₁ (a' q.1.2) * p₂ (a' q.1.1)) := by
      rw [hxsum, map_sum, map_sum, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, map_smul, map_smul, ← smul_sub, ← smul_sub, map_mul, map_mul, map_mul, hm _ (ha' _), hm _ (ha' _)]
      congr 1
      rw [add_mul, mul_add, mul_add, hanti _ (ha' q.1.1) _ (ha' q.1.2)]
      abel
    rw [← hm2, hmx, add_sub_cancel_left, sub_self]
  have hD0 : D = 0 := by
    have h := hK (by rw [hD, map_zero] : _ = DirectSum.toModule k (ℕ × ℕ) H' (fun p => kunnethMap 𝒜 p₁ p₂ p) 0)
    have := congrArg (fun W => W (1, 1)) h
    simpa [DirectSum.lof_apply] using this

  have hli1 : LinearIndependent k (fun l : Fin n => (⟨a' l, ha' l⟩ : ↥(𝒜 1))) :=
    LinearIndependent.of_comp (𝒜 1).subtype (by exact hli')
  obtain ⟨ψ, hψ⟩ := exists_dual_family _ hli1
  have hκ : ∀ q : PT, κ q = 0 := by
    intro q
    have h := congrArg (fun t => LinearMap.mul' k k (TensorProduct.map (ψ q.1.1) (ψ q.1.2) t)) hD0
    simp only [D, map_sum, map_smul, map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply, map_zero, hψ] at h
    rw [Finset.sum_eq_single q] at h
    · have hne : q.1.2 ≠ q.1.1 := ne_of_gt q.2
      simp only [if_true, if_neg hne, if_neg hne.symm, mul_one, mul_zero, sub_zero, smul_eq_mul] at h
      exact h
    · intro q' _ hq'
      have h1 : ¬ (q'.1.1 = q.1.1 ∧ q'.1.2 = q.1.2) := fun hh => hq' (Subtype.ext (Prod.ext hh.1 hh.2))
      have h2 : ¬ (q'.1.2 = q.1.1 ∧ q'.1.1 = q.1.2) := by
        rintro ⟨e1, e2⟩
        have := q'.2; rw [e1, e2] at this
        exact absurd (q.2.trans this) (lt_irrefl _)
      by_cases e1 : q'.1.1 = q.1.1
      · have e2 : ¬ q'.1.2 = q.1.2 := fun e2 => h1 ⟨e1, e2⟩
        by_cases e3 : q'.1.2 = q.1.1
        · have e4 : ¬ q'.1.1 = q.1.2 := fun e4 => h2 ⟨e3, e4⟩
          simp [e1, e2, e3, e4]
        · simp [e1, e2, e3]
      · by_cases e3 : q'.1.2 = q.1.1
        · have e4 : ¬ q'.1.1 = q.1.2 := fun e4 => h2 ⟨e3, e4⟩
          simp [e1, e3, e4]
        · simp [e1, e3]
    · intro h; exact absurd (Finset.mem_univ q) h
  rw [hxsum]
  exact Finset.sum_eq_zero fun q _ => by rw [hκ q, zero_smul]

end S_SetLike_GradedMonoid_eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective
end P2MW
export P2MW.S_SetLike_GradedMonoid_eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective (solution)
