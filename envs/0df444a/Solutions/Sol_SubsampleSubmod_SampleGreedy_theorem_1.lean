-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:58:55.313967+00:00
-- url     : https://prove2.me/submissions/8eece16c-3c8c-4ab3-a25d-e33d889b447f

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Model
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_4
import Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_8
import Theorems.Thm_OnlineCRS_Submod_lemma_3_7
import Theorems.Thm_SubsampleSubmod_SampleGreedy_display_4_1_1
import Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_10
import Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_9

/- Local probability, affine-normalization, and approximation helpers are inlined below.
The elementary split_coin_sum proof is reused from our checked coin-pairing work;
linear_marg follows the checked linear-removal proof with its empty-set offset retained.
The imported external Lemma 3.7 is attributed to vebis in the verification report. -/

namespace SubsampleSubmod.SampleGreedy.MainProof

open Finset

lemma weight_nonneg {α : Type} [Fintype α] (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (B : Finset α) : 0 ≤ sampleWeight q B := by
  exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.mpr hq1) _)

lemma weight_sum {α : Type} [Fintype α] (q : ℝ) :
    ∑ B : Finset α, sampleWeight q B = 1 := by
  simpa [sampleWeight] using Fintype.sum_pow_mul_eq_add_pow α q (1 - q)

-- The split is included locally from the checked coin-pairing proofs.
lemma split_coin_sum {α : Type} [Fintype α] [DecidableEq α] (u : α)
    (H : Finset α → ℝ) :
    (∑ B : Finset α, H B) =
      (∑ B ∈ ((Finset.univ : Finset α).erase u).powerset, H B) +
      ∑ B ∈ ((Finset.univ : Finset α).erase u).powerset, H (insert u B) := by
  have heq : insert u ((Finset.univ : Finset α).erase u) = Finset.univ :=
    Finset.insert_erase (Finset.mem_univ u)
  calc
    _ = ∑ B ∈ (insert u ((Finset.univ : Finset α).erase u)).powerset, H B := by
      rw [heq, Finset.powerset_univ]
    _ = _ := Finset.sum_powerset_insert (Finset.notMem_erase u Finset.univ) H

lemma weight_mem {α : Type} [Fintype α] [DecidableEq α] (q : ℝ) (u : α) :
    ∑ B : Finset α, sampleWeight q B * (if u ∈ B then 1 else 0) = q := by
  let U : Finset α := Finset.univ.erase u
  have hnot (B : Finset α) (hB : B ∈ U.powerset) : u ∉ B := by
    exact fun hu => (Finset.mem_erase.mp (Finset.mem_powerset.mp hB hu)).1 rfl
  have hcard : Fintype.card α = U.card + 1 := by
    simpa [U] using (Finset.card_erase_add_one (Finset.mem_univ u)).symm
  rw [split_coin_sum u]
  have hz : (∑ B ∈ U.powerset, sampleWeight q B * (if u ∈ B then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro B hB
    simp [hnot B hB]
  change (∑ B ∈ U.powerset, _) + (∑ B ∈ U.powerset, _) = q
  rw [hz, zero_add]
  have hs : (∑ B ∈ U.powerset, sampleWeight q (insert u B) *
      (if u ∈ insert u B then 1 else 0)) =
      q * ∑ B ∈ U.powerset, q ^ B.card * (1 - q) ^ (U.card - B.card) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    simp only [Finset.mem_insert_self, ↓reduceIte, mul_one, sampleWeight,
      Finset.card_insert_of_notMem (hnot B hB), hcard, Nat.add_sub_add_right, pow_succ]
    ring
  rw [hs, Finset.sum_pow_mul_eq_add_pow]
  simp

lemma pick_spec {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (u : α)
    (h : pick f I pool S = some u) :
    u ∈ pool ∧ u ∉ S ∧ I (insert u S) ∧ 0 < marg f u S := by
  classical
  unfold pick at h
  dsimp only at h
  split at h
  · rename_i hn
    have hm := Finset.min'_mem _ hn
    rw [Option.some.inj h] at hm
    exact Finset.mem_filter.mp (Finset.mem_filter.mp hm).1
  · cases h

lemma greedy_run {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hI : IsIndepSystem I) (B : Finset α) (j : ℕ) :
    I ((greedyStep f I B)^[j] ∅) ∧ ((greedyStep f I B)^[j] ∅) ⊆ B := by
  induction j with
  | zero => exact ⟨hI.1, Finset.empty_subset _⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    cases hp : pick f I B ((greedyStep f I B)^[j] ∅) with
    | none => simpa only [greedyStep, hp] using ih
    | some u =>
      have hs := pick_spec f I B _ u hp
      simpa only [greedyStep, hp] using And.intro hs.2.2.1 (Finset.insert_subset hs.1 ih.2)

lemma greedy_subset {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) : sampleGreedy f I B ⊆ B := by
  have h (j : ℕ) : ((greedyStep f I B)^[j] ∅) ⊆ B := by
    induction j with
    | zero => exact Finset.empty_subset _
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      cases hp : pick f I B ((greedyStep f I B)^[j] ∅) with
      | none => simpa only [greedyStep, hp] using ih
      | some u =>
        simpa only [greedyStep, hp] using Finset.insert_subset (pick_spec f I B _ u hp).1 ih
  exact h _

lemma pushforward_sum {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℝ) (F : Finset α → Finset α) (g : Finset α → ℝ) :
    (∑ R : Finset α, (∑ B : Finset α, w B * (if F B = R then 1 else 0)) * g R) =
      ∑ B : Finset α, w B * g (F B) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  simp

lemma E2_output {α : Type} [Fintype α] [LinearOrder α]
    (q : ℝ) (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α)
    (g : Finset α → ℝ) :
    E2 q f I T (fun st => g st.S) = ∑ B : Finset α, sampleWeight q B * g (sampleGreedy f I B) := by
  delta E2
  rw [← pushforward_sum (sampleWeight q) (fun B => (alg2 f I T B).S) g,
    ← pushforward_sum (sampleWeight q) (sampleGreedy f I) g]
  apply Finset.sum_congr rfl
  intro R _
  rw [lemma_4 f I q T R]

lemma union_submodular {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (T : Finset α) :
    NonmonotoneSubmod.Shared.Submodular (fun S => f (S ∪ T)) := by
  intro A B
  have h := hf (A ∪ T) (B ∪ T)
  have hu : (A ∪ T) ∪ (B ∪ T) = (A ∪ B) ∪ T := by ext e; simp; tauto
  have hi : (A ∪ T) ∩ (B ∪ T) = (A ∩ B) ∪ T := by ext e; simp; tauto
  rwa [hu, hi] at h

lemma union_lower {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hf0 : ∀ S, 0 ≤ f S)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (T : Finset α) :
    (1 - q) * f T ≤ E2 q f I T (fun st => f (st.S ∪ T)) := by
  classical
  let μ : Finset α → ℝ := fun R =>
    ∑ B : Finset α, sampleWeight q B * (if sampleGreedy f I B = R then 1 else 0)
  have hμ0 : ∀ R, 0 ≤ μ R := by
    intro R
    apply Finset.sum_nonneg
    intro B _
    exact mul_nonneg (weight_nonneg q hq0 hq1 B) (by split <;> norm_num)
  have hμ1 : ∑ R : Finset α, μ R = 1 := by
    simpa [μ] using (pushforward_sum (sampleWeight q) (sampleGreedy f I) (fun _ => 1)).trans
      (by simpa using weight_sum (α := α) q)
  have hμq (u : α) : ∑ R : Finset α, μ R * (if u ∈ R then 1 else 0) ≤ q := by
    change (∑ R : Finset α, (∑ B : Finset α, _) * _) ≤ q
    rw [pushforward_sum]
    calc
      _ ≤ ∑ B : Finset α, sampleWeight q B * (if u ∈ B then 1 else 0) := by
        apply Finset.sum_le_sum
        intro B _
        apply mul_le_mul_of_nonneg_left _ (weight_nonneg q hq0 hq1 B)
        split_ifs with hu hB hB
        · rfl
        · exact False.elim (hB (greedy_subset f I B hu))
        · norm_num
        · rfl
      _ = q := weight_mem q u
  have h := OnlineCRS.Submod.lemma_3_7 (fun S => f (S ∪ T)) (fun S => hf0 _)
    (union_submodular f hsub T) q hq0 hq1 μ hμ0 hμ1 hμq
  rw [E2_output q f I T (fun S => f (S ∪ T))]
  simpa only [Finset.empty_union, μ, pushforward_sum] using h

lemma monotone_union_lower {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hmono : Monotone f) (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (T : Finset α) :
    f T ≤ E2 q f I T (fun st => f (st.S ∪ T)) := by
  delta E2
  calc
    f T = ∑ B : Finset α, sampleWeight q B * f T := by rw [← Finset.sum_mul, weight_sum, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun B _ =>
      mul_le_mul_of_nonneg_left (hmono Finset.subset_union_right) (weight_nonneg q hq0 hq1 B)

end SubsampleSubmod.SampleGreedy.MainProof

namespace SubsampleSubmod.SampleGreedy.MainProof

open Finset

lemma linear_marg {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (hlin : IsLinear f) (u : α) (S : Finset α) (hu : u ∉ S) :
    marg f u S = f {u} - f ∅ := by
  have h := hlin ∅ S u (Finset.empty_subset _) hu
  simpa [marg] using h.symm

lemma marg_shift {α : Type} [DecidableEq α] (f : Finset α → ℝ) (c : ℝ)
    (u : α) (S : Finset α) : marg (fun A => f A - c) u S = marg f u S := by
  unfold marg
  ring

lemma pick_shift {α : Type} [LinearOrder α] (f : Finset α → ℝ) (I : Finset α → Prop)
    (c : ℝ) (pool S : Finset α) : pick (fun A => f A - c) I pool S = pick f I pool S := by
  classical
  unfold pick cands
  simp_rw [marg_shift]

lemma alg2_shift {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (c : ℝ) (T B : Finset α) :
    alg2 (fun A => f A - c) I T B = alg2 f I T B := by
  have hs : alg2Step (fun A => f A - c) I B = alg2Step f I B := by
    funext st
    unfold alg2Step
    rw [pick_shift]
  unfold alg2
  rw [hs]

lemma linear_shift {α : Type} [DecidableEq α] (f : Finset α → ℝ) (hlin : IsLinear f)
    (c : ℝ) : IsLinear (fun A => f A - c) := by
  intro A B e hAB he
  have h := hlin A B e hAB he
  dsimp
  linarith

lemma trace_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) (j : ℕ) :
    ∀ u : α, let st := (alg2Step f I B)^[j] (alg2Init T)
      (u ∈ st.considered → u ∉ st.Su u ∧ 0 < marg f u (st.Su u)) ∧
      (u ∉ st.considered → st.Ou u = ∅ ∧ u ∉ st.Y) := by
  classical
  induction j with
  | zero => simp [alg2Init]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    dsimp only
    let st := (alg2Step f I B)^[j] (alg2Init T)
    change ∀ u, (u ∈ (alg2Step f I B st).considered →
      u ∉ (alg2Step f I B st).Su u ∧ 0 < marg f u ((alg2Step f I B st).Su u)) ∧
      (u ∉ (alg2Step f I B st).considered → (alg2Step f I B st).Ou u = ∅ ∧
        u ∉ (alg2Step f I B st).Y)
    cases hp : pick f I st.rem st.S with
    | none => simpa only [alg2Step, hp, marg] using ih
    | some v =>
      have hv := pick_spec f I st.rem st.S v hp
      intro u
      by_cases huv : u = v
      · subst u
        by_cases hvB : v ∈ B <;> by_cases hvO : v ∈ st.O <;>
          simpa [alg2Step, hp, hvB, hvO, marg] using And.intro hv.2.1 hv.2.2.2
      · have hu := ih u
        change (u ∈ st.considered → u ∉ st.Su u ∧ 0 < marg f u (st.Su u)) ∧
          (u ∉ st.considered → st.Ou u = ∅ ∧ u ∉ st.Y) at hu
        by_cases hvB : v ∈ B <;> by_cases hvO : v ∈ st.O <;>
          simpa [alg2Step, hp, hvB, hvO, huv, marg] using hu

lemma trace {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) (u : α) :
    (u ∈ (alg2 f I T B).considered → u ∉ (alg2 f I T B).Su u ∧
      0 < marg f u ((alg2 f I T B).Su u)) ∧
    (u ∉ (alg2 f I T B).considered → (alg2 f I T B).Ou u = ∅ ∧ u ∉ (alg2 f I T B).Y) :=
  trace_run f I T B (Fintype.card α) u

lemma considered_marg {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hlin : IsLinear f) (T B : Finset α) (u : α) :
    (if u ∈ (alg2 f I T B).considered then (1 : ℝ) else 0) *
      marg f u ((alg2 f I T B).Su u) =
    (if u ∈ (alg2 f I T B).considered then (1 : ℝ) else 0) * (f {u} - f ∅) := by
  classical
  split_ifs with hu
  · rw [linear_marg f hlin u _ ((trace f I T B u).1 hu).1]
  · simp

lemma nonpositive_absent {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hlin : IsLinear f) (T B : Finset α) (u : α)
    (hu : f {u} - f ∅ ≤ 0) :
    u ∉ (alg2 f I T B).considered ∧ (alg2 f I T B).Ou u = ∅ ∧ u ∉ (alg2 f I T B).Y := by
  have hn : u ∉ (alg2 f I T B).considered := by
    intro hc
    have ht := (trace f I T B u).1 hc
    rw [linear_marg f hlin u _ ht.1] at ht
    linarith [ht.2]
  exact ⟨hn, (trace f I T B u).2 hn⟩

lemma E2_const {α : Type} [Fintype α] [LinearOrder α] (q : ℝ) (f : Finset α → ℝ)
    (I : Finset α → Prop) (T : Finset α) (c : ℝ) : E2 q f I T (fun _ => c) = c := by
  delta E2
  rw [← Finset.sum_mul, weight_sum, one_mul]

lemma E2_sub {α : Type} [Fintype α] [LinearOrder α] (q : ℝ) (f : Finset α → ℝ)
    (I : Finset α → Prop) (T : Finset α) (G H : Alg2State α → ℝ) :
    E2 q f I T (fun st => G st - H st) = E2 q f I T G - E2 q f I T H := by
  delta E2
  simp only [mul_sub, Finset.sum_sub_distrib]

lemma E2_sum {α : Type} [Fintype α] [LinearOrder α] (q : ℝ) (f : Finset α → ℝ)
    (I : Finset α → Prop) (T : Finset α) (G : α → Alg2State α → ℝ) :
    E2 q f I T (fun st => ∑ u : α, G u st) = ∑ u : α, E2 q f I T (G u) := by
  delta E2
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma E2_mul_const {α : Type} [Fintype α] [LinearOrder α] (q : ℝ) (f : Finset α → ℝ)
    (I : Finset α → Prop) (T : Finset α) (G : Alg2State α → ℝ) (c : ℝ) :
    E2 q f I T (fun st => G st * c) = E2 q f I T G * c := by
  delta E2
  simp only [← mul_assoc, Finset.sum_mul]

end SubsampleSubmod.SampleGreedy.MainProof

namespace SubsampleSubmod.SampleGreedy.MainProof

lemma union_upper {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (T : Finset α) (hT : I T) :
    E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f (st.S ∪ T)) ≤
      ((p : ℝ) + 1) * expectedValue (1 / ((p : ℝ) + 1)) f I := by
  have h := display_4_1_1 f I p hp hf0 hsub hI hext T hT
  have he : E2 (1 / ((p : ℝ) + 1)) f I T (fun st => f st.S) =
      expectedValue (1 / ((p : ℝ) + 1)) f I := E2_output _ f I T f
  rw [he] at h
  linarith [h.1, h.2.1, h.2.2]

lemma general_bound {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (T : Finset α) (hT : I T) :
    f T ≤ (((p : ℝ) + 1) ^ 2 / (p : ℝ)) * expectedValue (1 / ((p : ℝ) + 1)) f I := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hq0 : (0 : ℝ) ≤ 1 / ((p : ℝ) + 1) := by positivity
  have hq1 : 1 / ((p : ℝ) + 1) ≤ (1 : ℝ) := (div_le_one hd).mpr (by linarith)
  have hl := union_lower f I hf0 hsub _ hq0 hq1 T
  have hu := union_upper f I p hp hf0 hsub hI hext T hT
  have hc : 1 - 1 / ((p : ℝ) + 1) = (p : ℝ) / ((p : ℝ) + 1) := by
    field_simp
    ring
  rw [hc, div_mul_eq_mul_div] at hl
  have hs := (div_le_iff₀ hd).mp (hl.trans hu)
  calc
    f T ≤ (((p : ℝ) + 1) * expectedValue (1 / ((p : ℝ) + 1)) f I * ((p : ℝ) + 1)) / p := by
      apply (le_div_iff₀ hp0).mpr
      nlinarith [hs]
    _ = _ := by ring

lemma monotone_bound {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (hmono : Monotone f) (T : Finset α) (hT : I T) :
    f T ≤ ((p : ℝ) + 1) * expectedValue (1 / ((p : ℝ) + 1)) f I := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  exact (monotone_union_lower f I hmono _ (by positivity)
    ((div_le_one hd).mpr (by linarith)) T).trans (union_upper f I p hp hf0 hsub hI hext T hT)

end SubsampleSubmod.SampleGreedy.MainProof

namespace SubsampleSubmod.SampleGreedy.MainProof

open Finset

lemma weighted_charge {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hlin : IsLinear f)
    (hI : IsIndepSystem I) (hext : IsPExtendible p I) (T : Finset α) (hT : I T) (u : α) :
    E2 (1 / (p : ℝ)) f I T (fun st =>
      (((st.Ou u).card : ℝ) - (if u ∈ st.Y then (1 : ℝ) else 0)) * (f {u} - f ∅)) ≤
      (((p : ℝ) - 1) / (p : ℝ)) * E2 (1 / (p : ℝ)) f I T
        (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) := by
  classical
  by_cases hu : 0 ≤ f {u} - f ∅
  · have hm : E2 (1 / (p : ℝ)) f I T
        (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) =
        E2 (1 / (p : ℝ)) f I T (fun st => if u ∈ st.considered then (1 : ℝ) else 0) *
          (f {u} - f ∅) := by
      rw [← E2_mul_const]
      delta E2
      apply Finset.sum_congr rfl
      intro B _
      dsimp only
      rw [considered_marg f I hlin T B u]
    rw [E2_mul_const, hm]
    have h := mul_le_mul_of_nonneg_right (lemma_10 f I p hp hI hext T hT u) hu
    simpa only [mul_assoc] using h
  · have hu' : f {u} - f ∅ ≤ 0 := le_of_lt (lt_of_not_ge hu)
    have hl : E2 (1 / (p : ℝ)) f I T (fun st =>
        (((st.Ou u).card : ℝ) - (if u ∈ st.Y then (1 : ℝ) else 0)) * (f {u} - f ∅)) = 0 := by
      delta E2
      apply Finset.sum_eq_zero
      intro B _
      have hz := nonpositive_absent f I hlin T B u hu'
      simp [hz.2.1, hz.2.2]
    have hr : E2 (1 / (p : ℝ)) f I T
        (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) = 0 := by
      delta E2
      apply Finset.sum_eq_zero
      intro B _
      have hz := nonpositive_absent f I hlin T B u hu'
      simp [hz.1]
    rw [hl, hr, mul_zero]

lemma linear_bound_of_pathwise {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hlin : IsLinear f) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (T : Finset α) (hT : I T)
    (hpath : ∀ B : Finset α, f T - ∑ u : α,
      ((((alg2 f I T B).Ou u).card : ℝ) - (if u ∈ (alg2 f I T B).Y then (1 : ℝ) else 0)) *
        (f {u} - f ∅) ≤ f (alg2 f I T B).S) :
    f T ≤ (p : ℝ) * expectedValue (1 / (p : ℝ)) f I := by
  classical
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hq1 : 1 / (p : ℝ) ≤ (1 : ℝ) := (div_le_one hp0).mpr hp1
  have he : E2 (1 / (p : ℝ)) f I T (fun st => f T - ∑ u : α,
      (((st.Ou u).card : ℝ) - (if u ∈ st.Y then (1 : ℝ) else 0)) * (f {u} - f ∅)) ≤
        E2 (1 / (p : ℝ)) f I T (fun st => f st.S) := by
    delta E2
    exact Finset.sum_le_sum fun B _ =>
      mul_le_mul_of_nonneg_left (hpath B) (weight_nonneg _ hq0 hq1 B)
  rw [E2_sub, E2_const, E2_sum] at he
  have hb : (∑ u : α, E2 (1 / (p : ℝ)) f I T (fun st =>
      (((st.Ou u).card : ℝ) - (if u ∈ st.Y then (1 : ℝ) else 0)) * (f {u} - f ∅))) ≤
      (((p : ℝ) - 1) / p) * ∑ u : α, E2 (1 / (p : ℝ)) f I T
        (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u _ => weighted_charge f I p hp hlin hI hext T hT u
  have hcharge := lemma_8 f I hf0 (1 / (p : ℝ)) hq0 hq1 T
  have hx := mul_le_mul_of_nonneg_left hcharge (sub_nonneg.mpr hp1)
  have hc : ((p : ℝ) - 1) * (1 / (p : ℝ)) = ((p : ℝ) - 1) / (p : ℝ) := by ring
  rw [← mul_assoc, hc] at hx
  have htotal := hb.trans hx
  have hout : E2 (1 / (p : ℝ)) f I T (fun st => f st.S) =
      expectedValue (1 / (p : ℝ)) f I := E2_output _ f I T f
  rw [hout] at he htotal
  linarith

end SubsampleSubmod.SampleGreedy.MainProof

namespace SubsampleSubmod.SampleGreedy.MainProof

lemma offset_pathwise {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hlin : IsLinear f) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) :
    f T - ∑ u : α,
      ((((alg2 f I T B).Ou u).card : ℝ) - (if u ∈ (alg2 f I T B).Y then (1 : ℝ) else 0)) *
        (f {u} - f ∅) ≤ f (alg2 f I T B).S := by
  classical
  have h := lemma_9 (fun A => f A - f ∅) I (linear_shift f hlin (f ∅))
    (sub_self _) hI T hT B
  rw [alg2_shift] at h
  linarith

lemma linear_bound {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hlin : IsLinear f) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (T : Finset α) (hT : I T) :
    f T ≤ (p : ℝ) * expectedValue (1 / (p : ℝ)) f I :=
  linear_bound_of_pathwise f I p hp hf0 hlin hI hext T hT
    (offset_pathwise f I hlin hI T hT)

end SubsampleSubmod.SampleGreedy.MainProof

open SubsampleSubmod.SampleGreedy

theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hf0 : ∀ S, 0 ≤ f S)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) :
    (∀ N' : Finset α, I (sampleGreedy f I N')) ∧
    (∀ T : Finset α, I T →
      f T ≤ (((p : ℝ) + 1) ^ 2 / (p : ℝ)) * expectedValue (1 / ((p : ℝ) + 1)) f I) ∧
    (Monotone f → ∀ T : Finset α, I T →
      f T ≤ ((p : ℝ) + 1) * expectedValue (1 / ((p : ℝ) + 1)) f I) ∧
    (IsLinear f → ∀ T : Finset α, I T →
      f T ≤ (p : ℝ) * expectedValue (1 / (p : ℝ)) f I) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B
    exact (MainProof.greedy_run f I hI B (Fintype.card α)).1
  · exact MainProof.general_bound f I p hp hf0 hsub hI hext
  · exact MainProof.monotone_bound f I p hp hf0 hsub hI hext
  · intro hlin
    exact MainProof.linear_bound f I p hp hf0 hlin hI hext
