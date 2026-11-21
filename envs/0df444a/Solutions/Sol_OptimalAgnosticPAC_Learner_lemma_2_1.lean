-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:22:34.480873+00:00
-- url     : https://prove2.me/submissions/e4b05b6a-7f28-4390-8e4d-196a1e7c5ab5

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.Cube
open OptimalAgnosticPAC.Learner

variable {P : Type} [Fintype P]

/-- ordered pairs (v,p) with both v and its p-neighbour in U -/
noncomputable def A (U : Finset (P → Bool)) : Finset ((P → Bool) × P) :=
  (U ×ˢ (Finset.univ : Finset P)).filter (fun z => flipAt z.1 z.2 ∈ U)

theorem sum_A (U : Finset (P → Bool)) (f : (P → Bool) × P → ℝ) :
    ∑ v ∈ U, ∑ p ∈ dirs U v, f (v, p) = ∑ z ∈ A U, f z := by
  rw [A, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [dirs, Finset.sum_filter]

theorem sum_A_inv (U : Finset (P → Bool)) (f : (P → Bool) × P → ℝ) :
    ∑ z ∈ A U, f (flipAt z.1 z.2, z.2) = ∑ z ∈ A U, f z := by
  refine Finset.sum_nbij' (fun z => (flipAt z.1 z.2, z.2)) (fun z => (flipAt z.1 z.2, z.2))
    ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hz ⊢
    rw [flipAt_flipAt]; exact ⟨hz.2, hz.1⟩
  · intro z hz
    simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hz ⊢
    rw [flipAt_flipAt]; exact ⟨hz.2, hz.1⟩
  · intro z _; simp [flipAt_flipAt]
  · intro z _; simp [flipAt_flipAt]
  · intro z _; rfl

theorem two_edges_le (U : Finset (P → Bool)) :
    2 * (inducedEdges (cubeGraph P) U).card ≤ (A U).card := by
  let g : (P → Bool) × P → Sym2 (P → Bool) := fun z => s(z.1, flipAt z.1 z.2)
  have hsub : inducedEdges (cubeGraph P) U ⊆ (A U).image g := by
    intro e he
    simp only [inducedEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he1, he2⟩ := he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet] at he1
      obtain ⟨p, hp⟩ := he1
      have hu := he2 u (by simp)
      have hv := he2 v (by simp)
      simp only [Finset.mem_image, A, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true]
      refine ⟨(u, p), ⟨hu, by rw [← hp]; exact hv⟩, ?_⟩
      simp [g, hp]
  have h2 : 2 * ((A U).image g).card ≤ (A U).card := by
    refine Finset.mul_card_image_le_card (f := g) (A U) 2 ?_
    intro e he
    simp only [Finset.mem_image] at he
    obtain ⟨z, hz, rfl⟩ := he
    have hz' := hz
    simp only [A, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hz'
    have h1 : z ∈ (A U).filter (fun x => g x = g z) := by simp [hz]
    have h2 : (flipAt z.1 z.2, z.2) ∈ (A U).filter (fun x => g x = g z) := by
      simp only [Finset.mem_filter, A, Finset.mem_product, Finset.mem_univ, and_true]
      refine ⟨⟨hz'.2, ?_⟩, ?_⟩
      · rw [flipAt_flipAt]; exact hz'.1
      · simp only [g, flipAt_flipAt]; exact Sym2.eq_swap
    have hne : z ≠ (flipAt z.1 z.2, z.2) := by
      intro h; exact flipAt_ne z.1 z.2 (congrArg Prod.fst h)
    exact Finset.one_lt_card.2 ⟨z, h1, _, h2, hne⟩
  have := Finset.card_le_card hsub
  omega

/-- the double count: edges ≤ sum of weights, when w v p + w (flip v p) p = 1 -/
theorem edges_le_sum_w (U : Finset (P → Bool)) (w : (P → Bool) → P → ℝ)
    (hw : ∀ v p, w v p + w (flipAt v p) p = 1) :
    ((inducedEdges (cubeGraph P) U).card : ℝ) ≤ ∑ v ∈ U, ∑ p ∈ dirs U v, w v p := by
  have h1 : ∑ z ∈ A U, (w z.1 z.2 + w (flipAt z.1 z.2) z.2) = (A U).card := by
    rw [Finset.sum_congr rfl (fun z _ => hw z.1 z.2)]; simp
  have h2 : ∑ z ∈ A U, w (flipAt z.1 z.2) z.2 = ∑ z ∈ A U, w z.1 z.2 :=
    sum_A_inv U (fun z => w z.1 z.2)
  rw [Finset.sum_add_distrib, h2] at h1
  have h3 := sum_A U (fun z => w z.1 z.2)
  have h4 : (2 * (inducedEdges (cubeGraph P) U).card : ℝ) ≤ (A U).card := by
    exact_mod_cast two_edges_le U
  simp only at h3
  linarith
end OptimalAgnosticPAC.Dev.Cube
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L21
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.Cube

variable {P : Type} [Fintype P]

noncomputable def key (τ v f : P → Bool) : ℕ :=
  (Finset.univ.filter (fun p => τ p = true ∧ v p ≠ f p)).card

def Mset (F : Set (P → Bool)) (τ v : P → Bool) : Set (P → Bool) :=
  {f | f ∈ F ∧ ∀ g ∈ F, key τ v f ≤ key τ v g}

noncomputable def pick (F : Set (P → Bool)) (τ v : P → Bool) : P → Bool :=
  Classical.epsilon (fun f => f ∈ Mset F τ v)

theorem Mset_nonempty (F : Set (P → Bool)) (hF : F.Nonempty) (τ v : P → Bool) :
    (Mset F τ v).Nonempty := by
  have hfin : F.Finite := Set.toFinite F
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image hfin.toFinset (key τ v)
    (by simpa using hF)
  exact ⟨f, by simpa using hf, fun g hg => hmin g (by simpa using hg)⟩

theorem pick_spec (F : Set (P → Bool)) (hF : F.Nonempty) (τ v : P → Bool) :
    pick F τ v ∈ Mset F τ v := Classical.epsilon_spec (Mset_nonempty F hF τ v)

theorem pick_congr (F : Set (P → Bool)) (τ v v' : P → Bool)
    (h : ∀ p, τ p = true → v p = v' p) : pick F τ v = pick F τ v' := by
  have hk : ∀ f, key τ v f = key τ v' f := by
    intro f; unfold key
    congr 1; ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h p h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h p h1]; exact h2⟩
  have : Mset F τ v = Mset F τ v' := by
    ext f; simp only [Mset, Set.mem_setOf_eq, hk]
  unfold pick; rw [this]

noncomputable def ind (F : Set (P → Bool)) (τ v : P → Bool) (p : P) : ℝ :=
  if v p ≠ pick F τ v p ∧ τ p = false then 1 else 0

noncomputable def wt (F : Set (P → Bool)) (v : P → Bool) (p : P) : ℝ :=
  2 * (Fintype.card (P → Bool) : ℝ)⁻¹ * ∑ τ : P → Bool, ind F τ v p

theorem half_false (p : P) :
    ∑ τ : P → Bool, (if τ p = false then (1 : ℝ) else 0) = (Fintype.card (P → Bool) : ℝ) / 2 := by
  have h1 : ∑ τ : P → Bool, (if τ p = false then (1 : ℝ) else 0) =
      ∑ τ : P → Bool, (if τ p = true then (1 : ℝ) else 0) := by
    refine Fintype.sum_equiv ⟨fun τ => flipAt τ p, fun τ => flipAt τ p, fun τ => flipAt_flipAt τ p, fun τ => flipAt_flipAt τ p⟩ _ _ ?_
    intro τ
    simp [flipAt]
  have h2 : ∑ τ : P → Bool, (if τ p = false then (1 : ℝ) else 0) +
      ∑ τ : P → Bool, (if τ p = true then (1 : ℝ) else 0) = (Fintype.card (P → Bool) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    have : ∀ τ : P → Bool, ((if τ p = false then (1 : ℝ) else 0) +
        (if τ p = true then (1 : ℝ) else 0)) = 1 := by
      intro τ; cases τ p <;> simp
    simp [this]
  linarith

theorem half_true (p : P) :
    ∑ τ : P → Bool, (if τ p = true then (1 : ℝ) else 0) = (Fintype.card (P → Bool) : ℝ) / 2 := by
  have := half_false p
  have h2 : ∑ τ : P → Bool, (if τ p = false then (1 : ℝ) else 0) +
      ∑ τ : P → Bool, (if τ p = true then (1 : ℝ) else 0) = (Fintype.card (P → Bool) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    have : ∀ τ : P → Bool, ((if τ p = false then (1 : ℝ) else 0) +
        (if τ p = true then (1 : ℝ) else 0)) = 1 := by
      intro τ; cases τ p <;> simp
    simp [this]
  linarith

theorem card_pos : (0 : ℝ) < (Fintype.card (P → Bool) : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem wt_mem (F : Set (P → Bool)) (v : P → Bool) (p : P) : wt F v p ∈ Set.Icc (0 : ℝ) 1 := by
  have hN := card_pos (P := P)
  have h0 : 0 ≤ ∑ τ : P → Bool, ind F τ v p :=
    Finset.sum_nonneg (fun τ _ => by unfold ind; split_ifs <;> norm_num)
  have h1 : ∑ τ : P → Bool, ind F τ v p ≤ (Fintype.card (P → Bool) : ℝ) / 2 := by
    rw [← half_false p]
    refine Finset.sum_le_sum (fun τ _ => ?_)
    unfold ind
    by_cases h : τ p = false <;> by_cases h' : v p ≠ pick F τ v p <;> simp [h, h']
  constructor
  · unfold wt; positivity
  · unfold wt
    calc 2 * (Fintype.card (P → Bool) : ℝ)⁻¹ * ∑ τ : P → Bool, ind F τ v p
        ≤ 2 * (Fintype.card (P → Bool) : ℝ)⁻¹ * ((Fintype.card (P → Bool) : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp

theorem wt_flip (F : Set (P → Bool)) (hF : F.Nonempty) (v : P → Bool) (p : P) :
    wt F v p + wt F (flipAt v p) p = 1 := by
  have hN := card_pos (P := P)
  have key : ∀ τ : P → Bool, ind F τ v p + ind F τ (flipAt v p) p =
      (if τ p = false then (1 : ℝ) else 0) := by
    intro τ
    by_cases h : τ p = false
    · have hpk : pick F τ v = pick F τ (flipAt v p) := by
        refine pick_congr F τ v _ (fun q hq => ?_)
        have : q ≠ p := by rintro rfl; rw [h] at hq; exact absurd hq (by simp)
        simp [flipAt, Function.update_apply, this]
      unfold ind
      rw [← hpk]
      have : (flipAt v p) p = !(v p) := by simp [flipAt]
      rw [this]
      cases hv : v p <;> cases hk : pick F τ v p <;> simp [h]
    · unfold ind; simp [h]
  unfold wt
  rw [← mul_add, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun τ _ => key τ), half_false]
  field_simp
end OptimalAgnosticPAC.Dev.L21
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L21
open OptimalAgnosticPAC.Learner OptimalAgnosticPAC.Dev.Cube

variable {P : Type} [Fintype P]

noncomputable def eps (τ : P → Bool) (p : P) : ℝ := if τ p = true then -1 else 1

theorem ind_split (F : Set (P → Bool)) (τ v : P → Bool) (p : P) :
    ind F τ v p = (if τ p = true ∧ v p ≠ pick F τ v p then (1 : ℝ) else 0) +
      eps τ p * (if v p ≠ pick F τ v p then 1 else 0) := by
  unfold ind eps
  by_cases h1 : τ p = true <;> by_cases h2 : v p ≠ pick F τ v p <;> simp [h1, h2]

theorem sgn_id (τ v f : P → Bool) (p : P) :
    2 * (eps τ p * (if v p ≠ f p then (1 : ℝ) else 0)) =
      eps τ p + sgn (decide (τ p = v p)) * sgn (f p) := by
  unfold eps sgn
  cases h1 : τ p <;> cases h2 : v p <;> cases h3 : f p <;> simp [h1, h2, h3] <;> norm_num

theorem sum_eps (p : P) : ∑ τ : P → Bool, eps τ p = 0 := by
  have : ∀ τ : P → Bool, eps τ p = (if τ p = false then (1 : ℝ) else 0) -
      (if τ p = true then (1 : ℝ) else 0) := by
    intro τ; unfold eps; cases τ p <;> simp
  rw [Finset.sum_congr rfl (fun τ _ => this τ), Finset.sum_sub_distrib, half_false, half_true]
  ring

theorem sum_key (v f : P → Bool) :
    ∑ τ : P → Bool, (key τ v f : ℝ) = ((DIS v f).card : ℝ) * ((Fintype.card (P → Bool) : ℝ) / 2) := by
  have : ∀ τ : P → Bool, (key τ v f : ℝ) =
      ∑ p : P, (if τ p = true then (1 : ℝ) else 0) * (if v p ≠ f p then 1 else 0) := by
    intro τ
    unfold key
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h1 : τ p = true <;> by_cases h2 : v p ≠ f p <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun τ _ => this τ), Finset.sum_comm]
  have h2 : ∀ p : P, ∑ τ : P → Bool, (if τ p = true then (1 : ℝ) else 0) * (if v p ≠ f p then 1 else 0)
      = (if v p ≠ f p then 1 else 0) * ((Fintype.card (P → Bool) : ℝ) / 2) := by
    intro p
    rw [← Finset.sum_mul, half_true, mul_comm]
  rw [Finset.sum_congr rfl (fun p _ => h2 p), ← Finset.sum_mul]
  congr 1
  rw [DIS, Finset.card_filter]; push_cast; rfl

noncomputable def flipEquiv (v : P → Bool) : (P → Bool) ≃ (P → Bool) where
  toFun τ := fun p => decide (τ p = v p)
  invFun e := fun p => decide (e p = v p)
  left_inv τ := by funext p; cases h1 : τ p <;> cases h2 : v p <;> simp [h1, h2]
  right_inv e := by funext p; cases h1 : e p <;> cases h2 : v p <;> simp [h1, h2]

theorem wt_sum_le (F : Set (P → Bool)) (hF : F.Nonempty) (v : P → Bool) (D : Finset P) :
    ∑ p ∈ D, wt F v p ≤ (rho F v : ℝ) + width F D := by
  have hN := card_pos (P := P)
  obtain ⟨fs, hfs, hrho⟩ : ∃ f ∈ F, rho F v = (DIS v f).card := by
    have := Nat.sInf_mem (s := (fun f => (DIS v f).card) '' F) (hF.image _)
    obtain ⟨f, hf, h⟩ := this
    exact ⟨f, hf, h.symm⟩
  have hbdd : ∀ ε' : P → Bool, BddAbove ((fun f : P → Bool => ∑ p ∈ D, sgn (ε' p) * sgn (f p)) '' F) :=
    fun ε' => ((Set.toFinite F).image _).bddAbove
  -- pointwise bound
  have hpt : ∀ τ : P → Bool, 2 * ∑ p ∈ D, ind F τ v p ≤
      2 * (key τ v fs : ℝ) + ∑ p ∈ D, eps τ p +
        sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (flipEquiv v τ p) * sgn (f p)) '' F) := by
    intro τ
    have hmem := pick_spec F hF τ v
    simp only [Mset, Set.mem_setOf_eq] at hmem
    obtain ⟨hpF, hmin⟩ := hmem
    have hs1 : ∑ p ∈ D, (if τ p = true ∧ v p ≠ pick F τ v p then (1 : ℝ) else 0) ≤ (key τ v fs : ℝ) := by
      calc _ ≤ ∑ p : P, (if τ p = true ∧ v p ≠ pick F τ v p then (1 : ℝ) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => by split_ifs <;> norm_num)
        _ = (key τ v (pick F τ v) : ℝ) := by
            unfold key; rw [Finset.card_filter]; push_cast; rfl
        _ ≤ _ := by exact_mod_cast hmin fs hfs
    have hs2 : 2 * ∑ p ∈ D, eps τ p * (if v p ≠ pick F τ v p then (1 : ℝ) else 0) ≤
        ∑ p ∈ D, eps τ p + sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (flipEquiv v τ p) * sgn (f p)) '' F) := by
      rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun p _ => sgn_id τ v (pick F τ v) p), Finset.sum_add_distrib]
      gcongr
      exact le_csSup (hbdd _) ⟨pick F τ v, hpF, rfl⟩
    have : ∑ p ∈ D, ind F τ v p = ∑ p ∈ D, (if τ p = true ∧ v p ≠ pick F τ v p then (1 : ℝ) else 0) +
        ∑ p ∈ D, eps τ p * (if v p ≠ pick F τ v p then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun p _ => ind_split F τ v p)
    rw [this]; linarith
  -- average
  have hsum : ∑ p ∈ D, wt F v p = 2 * (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ τ : P → Bool, ∑ p ∈ D, ind F τ v p := by
    unfold wt
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hS : ∑ τ : P → Bool, 2 * ∑ p ∈ D, ind F τ v p ≤ ∑ τ : P → Bool,
      (2 * (key τ v fs : ℝ) + ∑ p ∈ D, eps τ p +
        sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (flipEquiv v τ p) * sgn (f p)) '' F)) :=
    Finset.sum_le_sum (fun τ _ => hpt τ)
  have hK : ∑ τ : P → Bool, (2 * (key τ v fs : ℝ) + ∑ p ∈ D, eps τ p +
        sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (flipEquiv v τ p) * sgn (f p)) '' F)) =
      (rho F v : ℝ) * (Fintype.card (P → Bool) : ℝ) +
        ∑ ε' : P → Bool, sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (ε' p) * sgn (f p)) '' F) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_key]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun p _ => sum_eps p)]
    simp only [Finset.sum_const_zero]
    rw [Fintype.sum_equiv (flipEquiv v) _ (fun ε' => sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (ε' p) * sgn (f p)) '' F)) (fun τ => rfl), hrho]
    ring
  rw [hsum]
  have : ∑ τ : P → Bool, ∑ p ∈ D, ind F τ v p ≤ ((rho F v : ℝ) * (Fintype.card (P → Bool) : ℝ) +
      ∑ ε' : P → Bool, sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (ε' p) * sgn (f p)) '' F)) / 2 := by
    rw [← hK]; rw [← Finset.mul_sum] at hS; linarith
  unfold width
  calc 2 * (Fintype.card (P → Bool) : ℝ)⁻¹ * ∑ τ : P → Bool, ∑ p ∈ D, ind F τ v p
      ≤ 2 * (Fintype.card (P → Bool) : ℝ)⁻¹ * (((rho F v : ℝ) * (Fintype.card (P → Bool) : ℝ) +
      ∑ ε' : P → Bool, sSup ((fun f : P → Bool => ∑ p ∈ D, sgn (ε' p) * sgn (f p)) '' F)) / 2) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by field_simp
end OptimalAgnosticPAC.Dev.L21
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Learner
open OptimalAgnosticPAC.Dev.L21 OptimalAgnosticPAC.Dev.Cube

theorem chk_lemma_2_1 {P : Type} [Fintype P] [Nonempty P] (F : Set (P → Bool)) (hF : F.Nonempty) :
    (∃ w : (P → Bool) → P → ℝ,
      (∀ v p, w v p ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ v p, w v p + w (flipAt v p) p = 1) ∧
      (∀ (v : P → Bool) (D : Finset P), ∑ p ∈ D, w v p ≤ (rho F v : ℝ) + width F D)) ∧
    (∀ U : Finset (P → Bool),
      ((inducedEdges (cubeGraph P) U).card : ℝ) ≤
        ∑ v ∈ U, ((rho F v : ℝ) + width F (dirs U v))) := by
  refine ⟨⟨wt F, wt_mem F, wt_flip F hF, wt_sum_le F hF⟩, fun U => ?_⟩
  exact (edges_le_sum_w U (wt F) (wt_flip F hF)).trans
    (Finset.sum_le_sum (fun v _ => wt_sum_le F hF v (dirs U v)))
end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_lemma_2_1 := @OptimalAgnosticPAC.Learner.chk_lemma_2_1
