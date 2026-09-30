-- Prove2me | solution 1 for UnderstandingML.contraction_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T15:56:48.762911+00:00
-- url     : https://prove2.me/submissions/02498c37-0a87-440e-8e6d-24fd5e5f714c

import Definitions.Def_UnderstandingML_Rademacher
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Bounded

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.ContractionAux

variable {m : ℕ}

/-- `2^m · m ·` (the Rademacher complexity) of an indexed family of vectors. -/
noncomputable def sumSup {ι : Type*} (v : ι → Fin m → ℝ) : ℝ :=
  ∑ σ : Fin m → Bool, ⨆ j, ∑ i, signVec σ i * v j i

/-- Flip the `k`-th sign. -/
def flipAt (k : Fin m) (σ : Fin m → Bool) : Fin m → Bool := Function.update σ k (!σ k)

lemma flipAt_involutive (k : Fin m) : Function.Involutive (flipAt k) := by
  intro σ; funext i
  by_cases h : i = k
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h]

lemma signVec_flipAt_self (k : Fin m) (σ : Fin m → Bool) :
    signVec (flipAt k σ) k = - signVec σ k := by
  unfold signVec flipAt; cases σ k <;> simp

lemma signVec_flipAt_ne (k : Fin m) (σ : Fin m → Bool) {i : Fin m} (hi : i ≠ k) :
    signVec (flipAt k σ) i = signVec σ i := by
  simp [signVec, flipAt, Function.update_of_ne hi]

/-- The part of `⟨σ, x⟩` coming from coordinates other than `k`. -/
noncomputable def rest (k : Fin m) (σ : Fin m → Bool) (x : Fin m → ℝ) : ℝ :=
  ∑ i, signVec σ i * (if i = k then 0 else x i)

lemma sum_eq_add_rest (k : Fin m) (σ : Fin m → Bool) (x : Fin m → ℝ) :
    ∑ i, signVec σ i * x i = signVec σ k * x k + rest k σ x := by
  unfold rest
  have : ∀ i, signVec σ i * x i =
      (if i = k then signVec σ k * x k else 0) + signVec σ i * (if i = k then 0 else x i) := by
    intro i; by_cases h : i = k
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl (fun i _ ↦ this i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma rest_flipAt (k : Fin m) (σ : Fin m → Bool) (x : Fin m → ℝ) :
    rest k (flipAt k σ) x = rest k σ x := by
  unfold rest
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  by_cases h : i = k
  · simp [h]
  · rw [signVec_flipAt_ne k σ h]

lemma sum_flip (k : Fin m) (F : (Fin m → Bool) → ℝ) :
    ∑ σ, F σ = ∑ σ, F (flipAt k σ) :=
  (Fintype.sum_equiv ((flipAt_involutive k).toPerm _) _ _ (fun _ ↦ rfl)).symm

/-- **One step of the contraction argument.** If two families agree off coordinate `k` and the
`k`-th coordinates of the first family are pairwise closer than those of the second, then the
Rademacher sum of the first is at most that of the second. -/
lemma sumSup_le_of_coord {ι : Type*} [Nonempty ι] (k : Fin m) (v w : ι → Fin m → ℝ)
    (hvw : ∀ j i, i ≠ k → v j i = w j i)
    (hk : ∀ j j', |v j k - v j' k| ≤ |w j k - w j' k|)
    (hw : ∀ σ, BddAbove (Set.range fun j ↦ ∑ i, signVec σ i * w j i)) :
    sumSup v ≤ sumSup w := by
  have hrest : ∀ σ j, rest k σ (v j) = rest k σ (w j) := by
    intro σ j; unfold rest
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    by_cases h : i = k
    · simp [h]
    · simp [h, hvw j i h]
  -- pointwise inequality for the pair `σ, flipAt k σ`
  have hpair : ∀ σ, (⨆ j, ∑ i, signVec σ i * v j i) +
      (⨆ j, ∑ i, signVec (flipAt k σ) i * v j i) ≤
      (⨆ j, ∑ i, signVec σ i * w j i) + (⨆ j, ∑ i, signVec (flipAt k σ) i * w j i) := by
    intro σ
    refine ciSup_add_ciSup_le (fun j j' ↦ ?_)
    rw [sum_eq_add_rest k σ (v j), sum_eq_add_rest k (flipAt k σ) (v j'),
      signVec_flipAt_self, rest_flipAt, hrest, hrest]
    have hs : signVec σ k = 1 ∨ signVec σ k = -1 := by
      unfold signVec; cases σ k <;> simp
    have h1 : signVec σ k * v j k + rest k σ (w j) + (-signVec σ k * v j' k + rest k σ (w j'))
        ≤ |w j k - w j' k| + rest k σ (w j) + rest k σ (w j') := by
      have : signVec σ k * (v j k - v j' k) ≤ |w j k - w j' k| := by
        refine le_trans ?_ (hk j j')
        rcases hs with hs | hs <;> rw [hs]
        · rw [one_mul]; exact le_abs_self _
        · rw [neg_one_mul]; exact neg_le_abs _
      nlinarith
    refine h1.trans ?_
    -- `|w j k − w j' k| + …` is attained by the pair `(j, j')` or `(j', j)`
    have hA : ∀ a b, signVec σ k * w a k + rest k σ (w a) +
        (-signVec σ k * w b k + rest k σ (w b)) ≤
        (⨆ j, ∑ i, signVec σ i * w j i) + (⨆ j, ∑ i, signVec (flipAt k σ) i * w j i) := by
      intro a b
      have e1 : ∑ i, signVec σ i * w a i ≤ ⨆ j, ∑ i, signVec σ i * w j i :=
        le_ciSup (hw σ) a
      have e2 : ∑ i, signVec (flipAt k σ) i * w b i ≤
          ⨆ j, ∑ i, signVec (flipAt k σ) i * w j i :=
        le_ciSup (hw (flipAt k σ)) b
      rw [sum_eq_add_rest k σ (w a)] at e1
      rw [sum_eq_add_rest k (flipAt k σ) (w b), signVec_flipAt_self, rest_flipAt] at e2
      linarith
    rcases hs with hs | hs
    · rcases le_total 0 (w j k - w j' k) with h | h
      · have := hA j j'; rw [hs] at this; rw [abs_of_nonneg h]; linarith
      · have := hA j' j; rw [hs] at this; rw [abs_of_nonpos h]; linarith
    · rcases le_total 0 (w j k - w j' k) with h | h
      · have := hA j' j; rw [hs] at this; rw [abs_of_nonneg h]; linarith
      · have := hA j j'; rw [hs] at this; rw [abs_of_nonpos h]; linarith
  have h2v : 2 * sumSup v = ∑ σ, ((⨆ j, ∑ i, signVec σ i * v j i) +
      (⨆ j, ∑ i, signVec (flipAt k σ) i * v j i)) := by
    unfold sumSup
    rw [Finset.sum_add_distrib, ← sum_flip k (fun σ ↦ ⨆ j, ∑ i, signVec σ i * v j i)]
    ring
  have h2w : 2 * sumSup w = ∑ σ, ((⨆ j, ∑ i, signVec σ i * w j i) +
      (⨆ j, ∑ i, signVec (flipAt k σ) i * w j i)) := by
    unfold sumSup
    rw [Finset.sum_add_distrib, ← sum_flip k (fun σ ↦ ⨆ j, ∑ i, signVec σ i * w j i)]
    ring
  have : 2 * sumSup v ≤ 2 * sumSup w := by
    rw [h2v, h2w]; exact Finset.sum_le_sum (fun σ _ ↦ hpair σ)
  linarith

lemma bddAbove_of_bound {ι : Type*} (v : ι → Fin m → ℝ) (C : ℝ) (hC : ∀ j i, |v j i| ≤ C)
    (σ : Fin m → Bool) : BddAbove (Set.range fun j ↦ ∑ i, signVec σ i * v j i) := by
  refine ⟨∑ _i : Fin m, C, ?_⟩
  rintro _ ⟨j, rfl⟩
  refine Finset.sum_le_sum (fun i _ ↦ ?_)
  have hs : |signVec σ i| = 1 := by unfold signVec; cases σ i <;> simp
  calc signVec σ i * v j i ≤ |signVec σ i * v j i| := le_abs_self _
    _ = |v j i| := by rw [abs_mul, hs, one_mul]
    _ ≤ C := hC j i

lemma iSup_image_eq {α β : Type*} (f : α → β) (A : Set α) (G : β → ℝ)
    (hb : BddAbove (Set.range fun a : A ↦ G (f a))) :
    (⨆ x : (f '' A), G x) = ⨆ a : A, G (f a) := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA; simp
  have : Nonempty A := hA.to_subtype
  have : Nonempty (f '' A) := (hA.image f).to_subtype
  have hb' : BddAbove (Set.range fun x : (f '' A) ↦ G x) := by
    obtain ⟨C, hC⟩ := hb
    refine ⟨C, ?_⟩
    rintro _ ⟨⟨x, a, ha, rfl⟩, rfl⟩
    exact hC ⟨⟨a, ha⟩, rfl⟩
  refine le_antisymm (ciSup_le fun ⟨x, a, ha, hx⟩ ↦ ?_) (ciSup_le fun a ↦ ?_)
  · subst hx; exact le_ciSup hb ⟨a, ha⟩
  · exact le_ciSup hb' ⟨f a, Set.mem_image_of_mem f a.2⟩

end UnderstandingML.ContractionAux

open UnderstandingML UnderstandingML.ContractionAux in
theorem solution {m : ℕ} (A : Set (Fin m → ℝ)) (hA : A.Nonempty)
    (hb : Bornology.IsBounded A) (ρ : NNReal) (φ : Fin m → ℝ → ℝ)
    (hφ : ∀ i, LipschitzWith ρ (φ i)) :
    rademacher ((fun a i ↦ φ i (a i)) '' A) ≤ ρ * rademacher A := by
  have : Nonempty A := hA.to_subtype
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  have hCa : ∀ a : A, ∀ i, |(a : Fin m → ℝ) i| ≤ C := fun a i ↦
    (norm_le_pi_norm (a : Fin m → ℝ) i).trans (hC a a.2)
  have hlip : ∀ i x y, |φ i x - φ i y| ≤ ρ * |x - y| := by
    intro i x y
    have := (hφ i).dist_le_mul x y
    simpa [Real.dist_eq] using this
  -- the interpolating families
  let V : ℕ → A → Fin m → ℝ := fun k a i ↦
    if (i : ℕ) < k then φ i ((a : Fin m → ℝ) i) else ρ * (a : Fin m → ℝ) i
  set B : ℝ := ∑ i, |φ i 0| + ρ * C with hB
  have hVb : ∀ k a i, |V k a i| ≤ B := by
    intro k a i
    have hρC : 0 ≤ (ρ : ℝ) * C := mul_nonneg ρ.2 ((abs_nonneg _).trans (hCa a i))
    have hsum : |φ i 0| ≤ ∑ i, |φ i 0| :=
      Finset.single_le_sum (f := fun i ↦ |φ i 0|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
    simp only [V]
    split_ifs
    · have h1 := hlip i ((a : Fin m → ℝ) i) 0
      rw [sub_zero] at h1
      have h2 : |φ i ((a : Fin m → ℝ) i)| ≤ |φ i 0| + ρ * |(a : Fin m → ℝ) i| := by
        have := abs_sub_abs_le_abs_sub (φ i ((a : Fin m → ℝ) i)) (φ i 0)
        linarith
      have h3 : (ρ : ℝ) * |(a : Fin m → ℝ) i| ≤ ρ * C := mul_le_mul_of_nonneg_left (hCa a i) ρ.2
      rw [hB]; linarith
    · rw [abs_mul, NNReal.abs_eq]
      have h3 : (ρ : ℝ) * |(a : Fin m → ℝ) i| ≤ ρ * C := mul_le_mul_of_nonneg_left (hCa a i) ρ.2
      have : 0 ≤ ∑ i, |φ i 0| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
      rw [hB]; linarith
  -- each step decreases the sum
  have hstep : ∀ k, k < m → sumSup (V (k + 1)) ≤ sumSup (V k) := by
    intro k hk
    refine sumSup_le_of_coord ⟨k, hk⟩ (V (k + 1)) (V k) ?_ ?_ (bddAbove_of_bound _ B (hVb k))
    · intro a i hi
      have : (i : ℕ) ≠ k := fun h ↦ hi (Fin.ext h)
      simp only [V]
      by_cases h : (i : ℕ) < k
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    · intro a a'
      simp only [V, lt_add_iff_pos_right, zero_lt_one, if_true, lt_irrefl, if_false]
      rw [← mul_sub, abs_mul, NNReal.abs_eq]
      exact hlip _ _ _
  have hchain : ∀ k, k ≤ m → sumSup (V k) ≤ sumSup (V 0) := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih => intro hk; exact (hstep k (by omega)).trans (ih (by omega))
  have hfin := hchain m le_rfl
  -- identify the two ends
  have hVm : sumSup (V m) = ∑ σ : Fin m → Bool,
      ⨆ x : ((fun a i ↦ φ i (a i)) '' A), ∑ i, signVec σ i * (x : Fin m → ℝ) i := by
    unfold sumSup
    refine Finset.sum_congr rfl (fun σ _ ↦ ?_)
    rw [iSup_image_eq (fun a i ↦ φ i (a i)) A (fun x ↦ ∑ i, signVec σ i * x i)]
    · simp only [V, Fin.is_lt, if_true]
    · have := bddAbove_of_bound (V m) B (hVb m) σ
      simpa only [V, Fin.is_lt, if_true] using this
  have hV0 : sumSup (V 0) = ρ * ∑ σ : Fin m → Bool,
      ⨆ a : A, ∑ i, signVec σ i * (a : Fin m → ℝ) i := by
    unfold sumSup
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ ↦ ?_)
    rw [Real.mul_iSup_of_nonneg (NNReal.coe_nonneg ρ)]
    refine iSup_congr (fun a ↦ ?_)
    simp only [V, Nat.not_lt_zero, if_false]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  unfold rademacher
  rw [← hVm]
  calc (1 / (m : ℝ)) * ((1 / 2 ^ m) * sumSup (V m))
      ≤ (1 / (m : ℝ)) * ((1 / 2 ^ m) * sumSup (V 0)) := by gcongr
    _ = ρ * ((1 / m) * ((1 / 2 ^ m) * ∑ σ : Fin m → Bool,
          ⨆ a : A, ∑ i, signVec σ i * (a : Fin m → ℝ) i)) := by rw [hV0]; ring
