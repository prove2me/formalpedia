-- Prove2me | solution 1 for SetLike.GradedMonoid.listProd_ne_zero_of_linearIndependent_of_kunneth_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4dd47d22-2346-5a88-813e-b342e0a02426

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SetLike_GradedMonoid_listProd_ne_zero_of_linearIndependent_of_kunneth_injective

set_option autoImplicit false

universe u

open TensorProduct DirectSum

namespace HopfBorelEngine

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

end HopfBorelEngine

theorem solution
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H] [Nontrivial H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hm : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x)
    {n : ℕ} (x : Fin n → H) (hx : ∀ i, x i ∈ 𝒜 1) (hli : LinearIndependent k x) :
    (List.ofFn x).prod ≠ 0 :=
  HopfBorelEngine.main 𝒜 p₁ p₂ m hanti hm hK n x hx hli

end S_SetLike_GradedMonoid_listProd_ne_zero_of_linearIndependent_of_kunneth_injective
end P2MW
export P2MW.S_SetLike_GradedMonoid_listProd_ne_zero_of_linearIndependent_of_kunneth_injective (solution)
