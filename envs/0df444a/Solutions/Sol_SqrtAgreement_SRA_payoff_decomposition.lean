-- Prove2me | solution 1 for SqrtAgreement.SRA.payoff_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:39:11.791813+00:00
-- url     : https://prove2.me/submissions/a3409e55-a93e-4b15-b59c-3bf3648020de

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

set_option autoImplicit false

open Finset SqrtAgreement.SRA

namespace SqrtAgreement.SRA.DecompProof

noncomputable def taskWeight {m k N M : ℕ} (G : GenModel m k) (Q : Profile N M k)
    (i : Fin N) (xi : Fin m) (yi : Fin M → Fin k) (ri : Fin M → Fin k) : ℝ :=
  G.PX xi * (∏ j', G.p xi (yi j')) * (∏ j', Q i j' (yi j') (ri j'))

theorem weight_eq_prod {m k N M : ℕ} (G : GenModel m k) (Q : Profile N M k)
    (x : Fin N → Fin m) (y : Fin N → Fin M → Fin k) (r : Reports N M k) :
    weight G Q x y r = ∏ i : Fin N, taskWeight G Q i (x i) (y i) (r i) := by
  unfold weight taskWeight
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

theorem sum_taskWeight_eq_one {m k N M : ℕ} {G : GenModel m k} (hG : G.Valid)
    {Q : Profile N M k} (i : Fin N) (hQi : ∀ j', Stoch (Q i j')) :
    ∑ xi : Fin m, ∑ yi : Fin M → Fin k, ∑ ri : Fin M → Fin k,
      taskWeight G Q i xi yi ri = 1 := by
  unfold taskWeight
  have hr : ∀ yi : Fin M → Fin k,
      ∑ ri : Fin M → Fin k, ∏ j', Q i j' (yi j') (ri j') = 1 := by
    intro yi
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun j' _ => (hQi j').2 (yi j')
  have hy : ∀ xi : Fin m,
      ∑ yi : Fin M → Fin k, ∏ j', G.p xi (yi j') = 1 := by
    intro xi
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun j' _ => hG.2.2.2 xi
  have h1 : ∀ xi : Fin m,
      (∑ yi : Fin M → Fin k, ∑ ri : Fin M → Fin k,
        G.PX xi * (∏ j', G.p xi (yi j')) * (∏ j', Q i j' (yi j') (ri j'))) = G.PX xi := by
    intro xi
    simp_rw [← Finset.mul_sum, hr, mul_one]
    rw [← Finset.mul_sum, hy, mul_one]
  simp_rw [h1]
  exact hG.2.1

theorem stoch_truthful (k : ℕ) : Stoch (truthful k) := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · unfold truthful; split_ifs <;> norm_num
  · rw [Finset.sum_eq_single a]
    · simp [truthful]
    · intro b _ hba; simp [truthful, hba]
    · intro ha; exact absurd (Finset.mem_univ a) ha

def splitAt {ι α : Type*} [DecidableEq ι] (i₀ : ι) :
    (ι → α) ≃ α × ({i : ι // i ≠ i₀} → α) where
  toFun f := (f i₀, fun i => f i.1)
  invFun p i := if h : i = i₀ then p.1 else p.2 ⟨i, h⟩
  left_inv f := by ext i; by_cases h : i = i₀ <;> simp [h]
  right_inv := fun ⟨a, g⟩ => Prod.ext (by simp) (by ext ⟨i, hi⟩; simp [hi])

theorem sum_splitAt {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (i₀ : ι) (F : (ι → α) → ℝ) :
    ∑ f : ι → α, F f =
      ∑ a : α, ∑ g : {i : ι // i ≠ i₀} → α, F ((splitAt i₀).symm (a, g)) := by
  rw [← Equiv.sum_comp (splitAt i₀).symm F, Fintype.sum_prod_type]

theorem prod_splitAt {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (F : ι → ℝ) :
    ∏ i : ι, F i = F i₀ * ∏ i : {i : ι // i ≠ i₀}, F i.1 := by
  rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ i₀)]
  congr 1
  have hset : Finset.univ.erase i₀ =
      (Finset.univ : Finset {i : ι // i ≠ i₀}).map ⟨Subtype.val, Subtype.val_injective⟩ := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hx; exact ⟨⟨x, hx.1⟩, Finset.mem_univ _, rfl⟩
    · rintro ⟨⟨y, hy⟩, -, rfl⟩; exact ⟨hy, Finset.mem_univ y⟩
  rw [hset, Finset.prod_map]
  rfl

theorem sum3_mul_sum3 {α₁ α₂ α₃ β₁ β₂ β₃ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype α₃] [Fintype β₁] [Fintype β₂] [Fintype β₃]
    (A : α₁ → α₂ → α₃ → ℝ) (B : β₁ → β₂ → β₃ → ℝ) :
    (∑ a₁, ∑ b₁, ∑ a₂, ∑ b₂, ∑ a₃, ∑ b₃, A a₁ a₂ a₃ * B b₁ b₂ b₃) =
      (∑ a₁, ∑ a₂, ∑ a₃, A a₁ a₂ a₃) * (∑ b₁, ∑ b₂, ∑ b₃, B b₁ b₂ b₃) := by
  have h3 : ∀ a₁ b₁ a₂ b₂ a₃,
      (∑ b₃, A a₁ a₂ a₃ * B b₁ b₂ b₃) = A a₁ a₂ a₃ * ∑ b₃, B b₁ b₂ b₃ :=
    fun _ _ _ _ _ => (Finset.mul_sum _ _ _).symm
  simp_rw [h3, ← Finset.sum_mul]
  have h2 : ∀ a₁ b₁ a₂,
      (∑ b₂, (∑ a₃, A a₁ a₂ a₃) * ∑ b₃, B b₁ b₂ b₃) =
        (∑ a₃, A a₁ a₂ a₃) * ∑ b₂, ∑ b₃, B b₁ b₂ b₃ :=
    fun _ _ _ => (Finset.mul_sum _ _ _).symm
  simp_rw [h2, ← Finset.sum_mul]
  have h1 : ∀ a₁,
      (∑ b₁, (∑ a₂, ∑ a₃, A a₁ a₂ a₃) * ∑ b₂, ∑ b₃, B b₁ b₂ b₃) =
        (∑ a₂, ∑ a₃, A a₁ a₂ a₃) * ∑ b₁, ∑ b₂, ∑ b₃, B b₁ b₂ b₃ :=
    fun _ => (Finset.mul_sum _ _ _).symm
  simp_rw [h1, ← Finset.sum_mul]

theorem e_indep_of_task {N M k : ℕ} (K : ℝ) (S : Setting N M) (j : Fin M)
    {i₀ : Fin N} (hi₀ : i₀ ∈ S.tasks j) (yy : Fin k)
    {r₁ r₂ : Reports N M k} (h : ∀ i, i ≠ i₀ → r₁ i = r₂ i) :
    e K S r₁ j yy = e K S r₂ j yy := by
  unfold e fbar
  congr 4
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ i₀ := fun heq => (Finset.mem_sdiff.mp hi).2 (heq ▸ hi₀)
  rw [h i hne]

theorem factor_at_task {m k N M : ℕ} (G : GenModel m k) (Q : Profile N M k)
    (i₀ : Fin N) (ydef : Fin k)
    (φ : (Fin M → Fin k) → ℝ) (ψ : Reports N M k → ℝ)
    (hψ : ∀ r₁ r₂ : Reports N M k, (∀ i, i ≠ i₀ → r₁ i = r₂ i) → ψ r₁ = ψ r₂) :
    (∑ x, ∑ y, ∑ r, weight G Q x y r * (φ (r i₀) * ψ r)) =
      (∑ x₀, ∑ y₀, ∑ r₀, taskWeight G Q i₀ x₀ y₀ r₀ * φ r₀) *
      (∑ xg : {i : Fin N // i ≠ i₀} → Fin m,
        ∑ yg : {i : Fin N // i ≠ i₀} → Fin M → Fin k,
          ∑ rg : {i : Fin N // i ≠ i₀} → Fin M → Fin k,
            (∏ i : {i : Fin N // i ≠ i₀}, taskWeight G Q i.1 (xg i) (yg i) (rg i)) *
              ψ ((splitAt i₀).symm (fun _ => ydef, rg))) := by
  rw [sum_splitAt i₀]
  simp_rw [sum_splitAt i₀]
  have hterm : ∀ (x₀ : Fin m) (xg : {i : Fin N // i ≠ i₀} → Fin m)
      (y₀ : Fin M → Fin k) (yg : {i : Fin N // i ≠ i₀} → Fin M → Fin k)
      (r₀ : Fin M → Fin k) (rg : {i : Fin N // i ≠ i₀} → Fin M → Fin k),
      weight G Q ((splitAt i₀).symm (x₀, xg)) ((splitAt i₀).symm (y₀, yg))
        ((splitAt i₀).symm (r₀, rg)) *
        (φ (((splitAt i₀).symm (r₀, rg)) i₀) * ψ ((splitAt i₀).symm (r₀, rg))) =
      (taskWeight G Q i₀ x₀ y₀ r₀ * φ r₀) *
        ((∏ i : {i : Fin N // i ≠ i₀}, taskWeight G Q i.1 (xg i) (yg i) (rg i)) *
          ψ ((splitAt i₀).symm (fun _ => ydef, rg))) := by
    intro x₀ xg y₀ yg r₀ rg
    rw [weight_eq_prod, prod_splitAt i₀]
    have hx0 : ((splitAt i₀).symm (x₀, xg)) i₀ = x₀ := by simp [splitAt]
    have hy0 : ((splitAt i₀).symm (y₀, yg)) i₀ = y₀ := by simp [splitAt]
    have hr0 : ((splitAt i₀).symm (r₀, rg)) i₀ = r₀ := by simp [splitAt]
    have hrest : (∏ i : {i : Fin N // i ≠ i₀},
        taskWeight G Q i.1 (((splitAt i₀).symm (x₀, xg)) i.1)
          (((splitAt i₀).symm (y₀, yg)) i.1) (((splitAt i₀).symm (r₀, rg)) i.1)) =
        ∏ i : {i : Fin N // i ≠ i₀}, taskWeight G Q i.1 (xg i) (yg i) (rg i) := by
      apply Finset.prod_congr rfl
      intro ⟨i, hi⟩ _
      simp [splitAt, hi]
    have hψ_eq : ψ ((splitAt i₀).symm (r₀, rg)) =
        ψ ((splitAt i₀).symm (fun _ => ydef, rg)) := by
      apply hψ
      intro i hi
      simp [splitAt, hi]
    rw [hx0, hy0, hr0, hrest, hψ_eq]
    ring
  let A : Fin m → (Fin M → Fin k) → (Fin M → Fin k) → ℝ :=
    fun x₀ y₀ r₀ => taskWeight G Q i₀ x₀ y₀ r₀ * φ r₀
  let B : ({i : Fin N // i ≠ i₀} → Fin m) → ({i : Fin N // i ≠ i₀} → Fin M → Fin k) →
      ({i : Fin N // i ≠ i₀} → Fin M → Fin k) → ℝ :=
    fun xg yg rg => (∏ i : {i : Fin N // i ≠ i₀}, taskWeight G Q i.1 (xg i) (yg i) (rg i)) *
      ψ ((splitAt i₀).symm (fun _ => ydef, rg))
  trans (∑ x₀, ∑ xg, ∑ y₀, ∑ yg, ∑ r₀, ∑ rg, A x₀ y₀ r₀ * B xg yg rg)
  · apply Finset.sum_congr rfl; intro x₀ _
    apply Finset.sum_congr rfl; intro xg _
    apply Finset.sum_congr rfl; intro y₀ _
    apply Finset.sum_congr rfl; intro yg _
    apply Finset.sum_congr rfl; intro r₀ _
    apply Finset.sum_congr rfl; intro rg _
    exact hterm x₀ xg y₀ yg r₀ rg
  · simp_rw [← Finset.mul_sum]
    simp_rw [← Finset.sum_mul]
    simp_rw [← Finset.mul_sum]
    simp_rw [← Finset.sum_mul]
    simp_rw [← Finset.mul_sum]
    simp_rw [← Finset.sum_mul]
    rfl

theorem expE_eq_of_agree_off {m k N M : ℕ} {G : GenModel m k} (hG : G.Valid)
    (K : ℝ) (S : Setting N M) (j : Fin M) {i₀ : Fin N} (hi₀ : i₀ ∈ S.tasks j)
    (ydef : Fin k) (yy : Fin k)
    {Q₁ Q₂ : Profile N M k} (hQ₁ : ProfileStoch Q₁) (hQ₂ : ProfileStoch Q₂)
    (hagree : ∀ i, i ≠ i₀ → Q₁ i = Q₂ i) :
    expE G K S Q₁ j yy = expE G K S Q₂ j yy := by
  have h1 : expE G K S Q₁ j yy =
      ∑ x, ∑ y, ∑ r, weight G Q₁ x y r * ((1 : ℝ) * e K S r j yy) := by
    unfold expE; simp
  have h2 : expE G K S Q₂ j yy =
      ∑ x, ∑ y, ∑ r, weight G Q₂ x y r * ((1 : ℝ) * e K S r j yy) := by
    unfold expE; simp
  rw [h1, h2,
    factor_at_task G Q₁ i₀ ydef (fun _ => 1) (fun r => e K S r j yy)
      (fun _ _ hr => e_indep_of_task K S j hi₀ yy hr),
    factor_at_task G Q₂ i₀ ydef (fun _ => 1) (fun r => e K S r j yy)
      (fun _ _ hr => e_indep_of_task K S j hi₀ yy hr)]
  simp only [mul_one, sum_taskWeight_eq_one hG i₀ (hQ₁ i₀),
    sum_taskWeight_eq_one hG i₀ (hQ₂ i₀), one_mul]
  apply Finset.sum_congr rfl; intro xg _
  apply Finset.sum_congr rfl; intro yg _
  apply Finset.sum_congr rfl; intro rg _
  congr 1
  apply Finset.prod_congr rfl
  intro ⟨i, hi⟩ _
  unfold taskWeight
  rw [hagree i hi]

def patchTasks {N M k : ℕ} (T : Finset (Fin N)) (Q' : Profile N M k) : Profile N M k :=
  fun i => if i ∈ T then symm (truthful k) i else Q' i

theorem expE_eq_truthful {m k N M : ℕ} {G : GenModel m k} (hG : G.Valid)
    (K : ℝ) (S : Setting N M) (j : Fin M) (ydef : Fin k) (yy : Fin k)
    {Q' : Profile N M k} (hQ' : IsDeviation S (symm (truthful k)) Q' j) :
    expE G K S Q' j yy = expE G K S (symm (truthful k)) j yy := by
  have hstoch_patch : ∀ T : Finset (Fin N), ProfileStoch (patchTasks T Q') := by
    intro T i j'
    unfold patchTasks
    split_ifs
    · exact stoch_truthful k
    · exact hQ'.1 i j'
  have hind : ∀ T : Finset (Fin N), T ⊆ S.tasks j →
      expE G K S (patchTasks T Q') j yy = expE G K S Q' j yy := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      have hemp : patchTasks (∅ : Finset (Fin N)) Q' = Q' := by ext i j' a b; simp [patchTasks]
      rw [hemp]
    | @insert i₁ T hi₁ ih =>
      intro hsub
      have hi₁_mem : i₁ ∈ S.tasks j := hsub (Finset.mem_insert_self i₁ T)
      have hT_sub : T ⊆ S.tasks j := (Finset.subset_insert i₁ T).trans hsub
      have hstep : expE G K S (patchTasks (insert i₁ T) Q') j yy =
          expE G K S (patchTasks T Q') j yy := by
        refine expE_eq_of_agree_off hG K S j hi₁_mem ydef yy
          (hstoch_patch (insert i₁ T)) (hstoch_patch T) ?_
        intro i hi
        simp [patchTasks, Finset.mem_insert, hi]
      exact hstep.trans (ih hT_sub)
  have hfull : patchTasks (S.tasks j) Q' = symm (truthful k) := by
    ext i j' a b
    unfold patchTasks
    split_ifs with hi
    · rfl
    · by_cases hjj' : j' = j
      · subst hjj'; rw [hQ'.2.2 i hi]
      · rw [hQ'.2.1 i j' hjj']
  have := hind (S.tasks j) Subset.rfl
  rw [hfull] at this
  exact this.symm

def indFactor {M k : ℕ} (j p : Fin M) (yy : Fin k) (j' : Fin M) (b : Fin k) : ℝ :=
  if j' = j ∨ j' = p then (if b = yy then 1 else 0) else 1

theorem ind_eq_prod_indFactor {M k : ℕ} (j p : Fin M) (yy : Fin k) (r₀ : Fin M → Fin k) :
    (if r₀ j = yy ∧ r₀ p = yy then (1 : ℝ) else 0) =
      ∏ j' : Fin M, indFactor j p yy j' (r₀ j') := by
  by_cases h : r₀ j = yy ∧ r₀ p = yy
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one
    intro j' _
    unfold indFactor
    rcases eq_or_ne j' j with rfl | hjj'
    · simp [h.1]
    · rcases eq_or_ne j' p with rfl | hjp
      · simp [h.2]
      · simp [hjj', hjp]
  · rw [if_neg h]
    symm
    by_cases hjy : r₀ j = yy
    · have hpy : r₀ p ≠ yy := fun hp => h ⟨hjy, hp⟩
      exact Finset.prod_eq_zero (Finset.mem_univ p) (by simp [indFactor, hpy])
    · exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [indFactor, hjy])

theorem task_agree_prob {m k N M : ℕ} {G : GenModel m k} (hG : G.Valid)
    {S : Setting N M} (hS : S.Legal) (j : Fin M) {i₀ : Fin N} (hi₀ : i₀ ∈ S.tasks j)
    (yy : Fin k) {Q' : Profile N M k} (hQ' : IsDeviation S (symm (truthful k)) Q' j) :
    (∑ x₀ : Fin m, ∑ y₀ : Fin M → Fin k, ∑ r₀ : Fin M → Fin k,
      taskWeight G Q' i₀ x₀ y₀ r₀ *
        (if r₀ j = yy ∧ r₀ (S.peer j i₀) = yy then 1 else 0)) =
      ∑ x₀ : Fin m, G.PX x₀ * G.p x₀ yy * ∑ y' : Fin k, G.p x₀ y' * Q' i₀ j y' yy := by
  set p := S.peer j i₀
  have hp_ne : p ≠ j := (hS.2.1 j i₀ hi₀).2
  have hQp : Q' i₀ p = truthful k := hQ'.2.1 i₀ p hp_ne
  apply Finset.sum_congr rfl
  intro x₀ _
  simp_rw [ind_eq_prod_indFactor j p yy]
  let rowVal : Fin M → Fin k → ℝ := fun j' a =>
    ∑ b : Fin k, Q' i₀ j' a b * indFactor j p yy j' b
  have hsum_r : ∀ y₀ : Fin M → Fin k,
      (∑ r₀ : Fin M → Fin k,
        taskWeight G Q' i₀ x₀ y₀ r₀ * ∏ j', indFactor j p yy j' (r₀ j')) =
      G.PX x₀ * ∏ j', (G.p x₀ (y₀ j') * rowVal j' (y₀ j')) := by
    intro y₀
    unfold taskWeight
    simp_rw [mul_assoc (G.PX x₀ * ∏ j', G.p x₀ (y₀ j')), ← Finset.prod_mul_distrib]
    rw [← Finset.mul_sum,
      ← Fintype.prod_sum (fun j' b => Q' i₀ j' (y₀ j') b * indFactor j p yy j' b),
      mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [hsum_r]
  rw [← Finset.mul_sum, ← Fintype.prod_sum (fun j' a => G.p x₀ a * rowVal j' a)]
  let colVal : Fin M → ℝ := fun j' => ∑ y' : Fin k, G.p x₀ y' * rowVal j' y'
  change G.PX x₀ * ∏ j' : Fin M, colVal j' =
    G.PX x₀ * G.p x₀ yy * ∑ y' : Fin k, G.p x₀ y' * Q' i₀ j y' yy
  have hcol_other : ∀ j' : Fin M, j' ∉ ({j, p} : Finset (Fin M)) → colVal j' = 1 := by
    intro j' hj'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
    have hrow1 : ∀ y' : Fin k, rowVal j' y' = 1 := by
      intro y'
      simp only [rowVal, indFactor, hj'.1, hj'.2, or_self, ite_false, mul_one]
      exact (hQ'.1 i₀ j').2 y'
    simp only [colVal, hrow1, mul_one]
    exact hG.2.2.2 x₀
  have hprod_pair : (∏ j' : Fin M, colVal j') = colVal j * colVal p := by
    rw [← Finset.prod_subset (Finset.subset_univ ({j, p} : Finset (Fin M)))
      (fun j' _ hj' => hcol_other j' hj')]
    exact Finset.prod_pair hp_ne.symm
  have hcol_j : colVal j = ∑ y' : Fin k, G.p x₀ y' * Q' i₀ j y' yy := by
    simp only [colVal, rowVal, indFactor, true_or, ite_true]
    apply Finset.sum_congr rfl
    intro y' _
    simp
  have hcol_p : colVal p = G.p x₀ yy := by
    simp only [colVal, rowVal, indFactor, or_true, ite_true, hQp, truthful]
    have hp_in : ∀ y' : Fin k,
        (∑ b : Fin k, (if b = y' then (1 : ℝ) else 0) * if b = yy then 1 else 0) =
          if yy = y' then 1 else 0 := by
      intro y'; simp [eq_comm]
    simp_rw [hp_in]
    simp
  rw [hprod_pair, hcol_j, hcol_p]
  ring

theorem sum3_comm_finset {α₁ α₂ α₃ γ : Type*} [Fintype α₁] [Fintype α₂] [Fintype α₃]
    (s : Finset γ) (F : α₁ → α₂ → α₃ → γ → ℝ) :
    (∑ a₁, ∑ a₂, ∑ a₃, ∑ c ∈ s, F a₁ a₂ a₃ c) =
      ∑ c ∈ s, ∑ a₁, ∑ a₂, ∑ a₃, F a₁ a₂ a₃ c := by
  have h3 : ∀ a₁ a₂, (∑ a₃, ∑ c ∈ s, F a₁ a₂ a₃ c) = ∑ c ∈ s, ∑ a₃, F a₁ a₂ a₃ c :=
    fun _ _ => Finset.sum_comm
  simp_rw [h3]
  have h2 : ∀ a₁, (∑ a₂, ∑ c ∈ s, ∑ a₃, F a₁ a₂ a₃ c) = ∑ c ∈ s, ∑ a₂, ∑ a₃, F a₁ a₂ a₃ c :=
    fun _ => Finset.sum_comm
  simp_rw [h2]
  exact Finset.sum_comm

end SqrtAgreement.SRA.DecompProof

open SqrtAgreement.SRA.DecompProof in
theorem solution {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M)
    (hG : G.Valid) (hS : S.Legal) (j : Fin M) (_hN : (S.tasks j).card < N)
    (Q' : Profile N M k) (hQ' : IsDeviation S (symm (truthful k)) Q' j) :
    expPay G K S Q' j =
      ∑ i ∈ S.tasks j, ∑ y : Fin k, expE G K S (symm (truthful k)) j y *
        ∑ x : Fin m, G.PX x * G.p x y * ∑ y' : Fin k, G.p x y' * Q' i j y' y := by
  have hm : 0 < m := by
    by_contra hm0
    have hm_eq : m = 0 := by omega
    subst hm_eq
    have := hG.2.1
    simp at this
  have hk : 0 < k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    subst hk_eq
    have := hG.2.2.2 ⟨0, hm⟩
    simp at this
  let ydef : Fin k := ⟨0, hk⟩
  unfold expPay tau
  simp_rw [Finset.mul_sum]
  rw [sum3_comm_finset (S.tasks j)]
  apply Finset.sum_congr rfl
  intro i₀ hi₀
  have hsplit_yy : ∀ r : Reports N M k,
      (if r i₀ j = r i₀ (S.peer j i₀) then e K S r j (r i₀ j) else 0) =
        ∑ yy : Fin k,
          (if r i₀ j = yy ∧ r i₀ (S.peer j i₀) = yy then (1 : ℝ) else 0) * e K S r j yy := by
    intro r
    by_cases heq : r i₀ j = r i₀ (S.peer j i₀)
    · rw [if_pos heq]
      symm
      rw [Finset.sum_eq_single (r i₀ j)]
      · simp [heq.symm]
      · intro yy _ hyy
        have : ¬ (r i₀ j = yy ∧ r i₀ (S.peer j i₀) = yy) := fun ⟨h1, _⟩ => hyy h1.symm
        simp [this]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · rw [if_neg heq]
      symm
      apply Finset.sum_eq_zero
      intro yy _
      have : ¬ (r i₀ j = yy ∧ r i₀ (S.peer j i₀) = yy) :=
        fun ⟨h1, h2⟩ => heq (h1.trans h2.symm)
      simp [this]
  simp_rw [hsplit_yy, Finset.mul_sum]
  rw [sum3_comm_finset Finset.univ]
  apply Finset.sum_congr rfl
  intro yy _
  have hfac1 := factor_at_task G Q' i₀ ydef
    (fun r₀ => if r₀ j = yy ∧ r₀ (S.peer j i₀) = yy then (1 : ℝ) else 0)
    (fun r => e K S r j yy)
    (fun _ _ hr => e_indep_of_task K S j hi₀ yy hr)
  have hfac2 := factor_at_task G Q' i₀ ydef
    (fun _ => 1)
    (fun r => e K S r j yy)
    (fun _ _ hr => e_indep_of_task K S j hi₀ yy hr)
  simp only [mul_one, one_mul, sum_taskWeight_eq_one hG i₀ (hQ'.1 i₀)] at hfac2
  have hexpE_Q' : expE G K S Q' j yy =
      ∑ xg : {i : Fin N // i ≠ i₀} → Fin m,
        ∑ yg : {i : Fin N // i ≠ i₀} → Fin M → Fin k,
          ∑ rg : {i : Fin N // i ≠ i₀} → Fin M → Fin k,
            (∏ i : {i : Fin N // i ≠ i₀}, taskWeight G Q' i.1 (xg i) (yg i) (rg i)) *
              e K S ((splitAt i₀).symm (fun _ => ydef, rg)) j yy := hfac2
  rw [hfac1, ← hexpE_Q', task_agree_prob hG hS j hi₀ yy hQ',
    expE_eq_truthful hG K S j ydef yy hQ', mul_comm]
  simp_rw [Finset.mul_sum]
