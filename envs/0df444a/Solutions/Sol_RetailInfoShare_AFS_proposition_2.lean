-- Prove2me | solution 1 for RetailInfoShare.AFS.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:44:02.344842+00:00
-- url     : https://prove2.me/submissions/a91f3286-943c-4317-be19-1a337a0971b9

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
import Theorems.Thm_RetailInfoShare_AFS_eq_8_general_K
import Theorems.Thm_RetailInfoShare_AFS_endpoint_noise_level
import Theorems.Thm_RetailInfoShare_AFS_integer_comparison
import Theorems.Thm_RetailInfoShare_AFS_informed_sellers_gain
import Theorems.Thm_RetailInfoShare_AFS_lemma_1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS.Prop2Aux

open RetailInfoShare.AFS

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Relabeling the sellers -/

/-- Reindexing of the primitive random variables along a permutation of the sellers. -/
def primMap (σ : Equiv.Perm (Fin P.N)) : Prim P.N → Prim P.N
  | .u => .u
  | .e i => .e (σ i)
  | .ξ i j => .ξ (σ i) (σ j)

lemma primMap_injective (σ : Equiv.Perm (Fin P.N)) : Function.Injective (primMap (P := P) σ) := by
  intro x y h
  cases x <;> cases y <;> simp_all [primMap]

/-- The primitives with the sellers relabeled by `σ`. -/
noncomputable def relabel (Z : Primitives P Ω μ) (σ : Equiv.Perm (Fin P.N)) :
    Primitives P Ω μ where
  u := Z.u
  e i := Z.e (σ i)
  ξ i j := Z.ξ (σ i) (σ j)
  isProb := Z.isProb
  meas_u := Z.meas_u
  meas_e i := Z.meas_e (σ i)
  meas_ξ i j := Z.meas_ξ (σ i) (σ j)
  law_u := Z.law_u
  law_e i := Z.law_e (σ i)
  law_ξ i j := Z.law_ξ (σ i) (σ j)
  indep := by
    have h := Z.indep.precomp (primMap_injective (P := P) σ)
    convert h using 2 with k
    cases k <;> rfl

/-- The noise matrix with the sellers relabeled by `σ`. -/
def relabelM (M : NoiseMatrix P.N) (σ : Equiv.Perm (Fin P.N)) : NoiseMatrix P.N :=
  fun i j => M (σ i) (σ j)

lemma info_relabel (Z : Primitives P Ω μ) (M : NoiseMatrix P.N) (σ : Equiv.Perm (Fin P.N))
    (j : Fin P.N) : info (relabel Z σ) (relabelM M σ) j = info Z M (σ j) := by
  unfold info
  exact σ.iSup_comp (g := fun i => ⨆ (_ : M i (σ j) ≠ ⊤),
    MeasurableSpace.comap (xhat Z M i (σ j)) inferInstance)

lemma sum_erase_perm (σ : Equiv.Perm (Fin P.N)) (f : Fin P.N → ℝ) (i : Fin P.N) :
    ∑ d ∈ Finset.univ.erase i, f (σ d) = ∑ d ∈ Finset.univ.erase (σ i), f d := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_erase_eq_sub (Finset.mem_univ _),
    Equiv.sum_comp σ f]

lemma price_relabel (Z : Primitives P Ω μ) (σ : Equiv.Perm (Fin P.N))
    (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) :
    price (relabel Z σ) (fun d => Q (σ d)) i = price Z Q (σ i) := by
  funext ω
  unfold price
  rw [sum_erase_perm σ (fun d => Q d ω) i]
  rfl

lemma sellerProfit_relabel (Z : Primitives P Ω μ) (σ : Equiv.Perm (Fin P.N))
    (Q : Fin P.N → Ω → ℝ) (i : Fin P.N) :
    sellerProfit (relabel Z σ) (fun d => Q (σ d)) i = sellerProfit Z Q (σ i) := by
  unfold sellerProfit
  rw [price_relabel]

lemma platformProfit_relabel (Z : Primitives P Ω μ) (σ : Equiv.Perm (Fin P.N))
    (Q : Fin P.N → Ω → ℝ) :
    platformProfit (relabel Z σ) (fun d => Q (σ d)) = platformProfit Z Q := by
  unfold platformProfit
  congr 1
  funext ω
  congr 1
  simp_rw [price_relabel]
  exact Equiv.sum_comp σ (fun i => Q i ω * price Z Q i ω)

lemma isEquilibrium_relabel (Z : Primitives P Ω μ) (M : NoiseMatrix P.N)
    (σ : Equiv.Perm (Fin P.N)) (Q : Fin P.N → Ω → ℝ) (hQ : IsEquilibrium Z M Q) :
    IsEquilibrium (relabel Z σ) (relabelM M σ) (fun d => Q (σ d)) := by
  have hadm : ∀ j q, IsAdmissible (relabel Z σ) (relabelM M σ) j q ↔
      IsAdmissible Z M (σ j) q := by
    intro j q
    unfold IsAdmissible
    rw [info_relabel]
  refine ⟨fun j => (hadm j _).2 (hQ.1 (σ j)), fun j q hq => ?_⟩
  have hupd : Function.update (fun d => Q (σ d)) j q =
      fun d => Function.update Q (σ j) q (σ d) := by
    have := Function.update_comp_equiv Q σ (σ j) q
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  rw [hupd, sellerProfit_relabel, sellerProfit_relabel]
  exact hQ.2 (σ j) q ((hadm j q).1 hq)

/-- A permutation sending the first `S.card` sellers onto `S`. -/
lemma exists_perm (S : Finset (Fin P.N)) :
    ∃ σ : Equiv.Perm (Fin P.N), ∀ j, σ j ∈ S ↔ (j : ℕ) < S.card := by
  have hK : S.card ≤ P.N := by
    simpa using Finset.card_le_univ S
  have c1 : Fintype.card {j : Fin P.N // (j : ℕ) < S.card} = Fintype.card {j // j ∈ S} := by
    have e : {j : Fin P.N // (j : ℕ) < S.card} ≃ Fin S.card :=
      { toFun := fun j => ⟨j.1.val, j.2⟩
        invFun := fun k => ⟨⟨k.val, lt_of_lt_of_le k.2 hK⟩, k.2⟩
        left_inv := fun j => rfl
        right_inv := fun k => rfl }
    rw [Fintype.card_congr e, Fintype.card_fin, Fintype.card_coe]
  have c2 : Fintype.card {j : Fin P.N // ¬ (j : ℕ) < S.card} =
      Fintype.card {j // ¬ j ∈ S} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
  let e1 := Fintype.equivOfCardEq c1
  let e2 := Fintype.equivOfCardEq c2
  refine ⟨Equiv.subtypeCongr e1 e2, fun j => ?_⟩
  by_cases h : (j : ℕ) < S.card
  · have : Equiv.subtypeCongr e1 e2 j = (e1 ⟨j, h⟩ : Fin P.N) := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, h]
    rw [this]
    exact ⟨fun _ => h, fun _ => (e1 ⟨j, h⟩).2⟩
  · have : Equiv.subtypeCongr e1 e2 j = (e2 ⟨j, h⟩ : Fin P.N) := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, h]
    rw [this]
    exact ⟨fun h' => absurd h' (e2 ⟨j, h⟩).2, fun h' => absurd h' h⟩

/-- Truthful full sharing with an arbitrary group `S` yields the eq. (8) profit with `|S|`. -/
lemma profit_group (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) (S : Finset (Fin P.N))
    (Q : Fin P.N → Ω → ℝ)
    (hQ : IsEquilibrium Z (fun _ j => if j ∈ S then 0 else ⊤) Q) :
    platformProfit Z Q = PiNS P + sharingGain P S.card := by
  obtain ⟨σ, hσ⟩ := exists_perm (P := P) S
  have hM : relabelM (fun _ j => if j ∈ S then (0 : ℝ≥0∞) else ⊤) σ =
      truthfulGroup P.N S.card := by
    funext i j
    simp only [relabelM, truthfulGroup, hσ j]
  have hQ' := isEquilibrium_relabel Z _ σ Q hQ
  rw [hM] at hQ'
  have hK : S.card ≤ P.N := by simpa using Finset.card_le_univ S
  have := (eq_8_general_K P hP μ (relabel Z σ) S.card hK).2 _ hQ'
  rw [platformProfit_relabel] at this
  exact this

/-! ### Interior columns -/

/-- Columns of `M` containing an entry outside `{0, ⊤}`. -/
noncomputable def interior (M : NoiseMatrix P.N) : Finset (Fin P.N) :=
  by classical exact Finset.univ.filter (fun j => ¬ ∀ i, (M i j = 0 ∨ M i j = ⊤))

lemma setColumn_isAFS (M : NoiseMatrix P.N) (hM : IsAFS M) (j : Fin P.N) (η : ℝ≥0∞) :
    IsAFS (setColumn M j η) := by
  intro i₁ i₂ j'
  unfold setColumn
  split_ifs
  · rfl
  · exact hM i₁ i₂ j'

/-- Every equilibrium of every AFS matrix gives at most the profit of the best group. -/
lemma bound (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) (B : ℝ)
    (hB : ∀ S : Finset (Fin P.N), PiNS P + sharingGain P S.card ≤ B) :
    ∀ (n : ℕ) (M : NoiseMatrix P.N), (interior M).card = n → IsAFS M →
      ∀ Q, IsEquilibrium Z M Q → platformProfit Z Q ≤ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hn hM Q hQ
  classical
  by_cases hI : interior M = ∅
  · -- every column is all-zero or all-infinite
    have hcol : ∀ i j, M i j = 0 ∨ M i j = ⊤ := by
      intro i j
      by_contra h
      have : j ∈ interior M := by
        simp only [interior, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h'; exact h (h' i)
      rw [hI] at this; simp at this
    let S : Finset (Fin P.N) := Finset.univ.filter (fun j => M j j = 0)
    have hMS : M = fun _ j => if j ∈ S then 0 else ⊤ := by
      funext i j
      have hij : M i j = M j j := hM i j j
      by_cases h : M j j = 0
      · have : j ∈ S := by simp [S, h]
        rw [if_pos this, hij, h]
      · have : j ∉ S := by simp [S, h]
        rw [if_neg this, hij]
        exact (hcol j j).resolve_left h
    rw [hMS] at hQ
    rw [profit_group P hP μ Z S Q hQ]
    exact hB S
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hI
    have hj' := hj
    simp only [interior, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
    push Not at hj'
    obtain ⟨i, hi0, hitop⟩ := hj'
    set η := M i j
    have hMeq : setColumn M j η = M := by
      funext i' j'
      unfold setColumn
      split_ifs with h
      · subst h; exact hM i i' j'
      · rfl
    have hQ1 : IsEquilibrium Z (setColumn M j η) Q := by rw [hMeq]; exact hQ
    obtain ⟨η', hη', Q', hQ', hlt⟩ :=
      endpoint_noise_level P hP μ Z M hM j η hi0 hitop Q hQ1
    have hsub : interior (setColumn M j η') ⊂ interior M := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j, hj, ?_⟩
        simp only [interior, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        intro i'
        simp only [setColumn]
        exact hη'
      · intro j' hj''
        simp only [interior, Finset.mem_filter, Finset.mem_univ, true_and] at hj'' ⊢
        by_cases h : j' = j
        · subst h
          exfalso; apply hj''
          intro i'
          simp only [setColumn]
          exact hη'
        · intro h'
          apply hj''
          intro i'
          simp only [setColumn, if_neg h]
          exact h' i'
    have hcard := Finset.card_lt_card hsub
    have := ih _ (hn ▸ hcard) (setColumn M j η') rfl (setColumn_isAFS M hM j η') Q' hQ'
    linarith

end RetailInfoShare.AFS.Prop2Aux

open RetailInfoShare.AFS RetailInfoShare.AFS.Prop2Aux in
theorem solution (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) :
    (∃ K : ℕ, (K = ⌊mStar P⌋₊ ∨ K = ⌈mStar P⌉₊) ∧
        IsOptimalAFS Z (truthfulGroup P.N K) ∧
        (∀ Q, IsEquilibrium Z (truthfulGroup P.N K) Q →
          platformProfit Z Q = PiNS P + sharingGain P K) ∧
        (∀ Q Q₀, IsEquilibrium Z (truthfulGroup P.N K) Q →
          IsEquilibrium Z (noSharing P.N) Q₀ →
          platformProfit Z Q₀ ≤ platformProfit Z Q ∧
            ∀ i, sellerProfit Z Q₀ i ≤ sellerProfit Z Q i)) ∧
    (∀ K : ℕ, K ≤ P.N → IsOptimalAFS Z (truthfulGroup P.N K) →
      K = ⌊mStar P⌋₊ ∨ K = ⌈mStar P⌉₊) := by
  obtain ⟨⟨K, hKfc, hKN, hKmax⟩, hconv⟩ := integer_comparison P hP
  have hAFS : ∀ K', IsAFS (truthfulGroup P.N K') := fun _ _ _ _ => rfl
  have hgain0 : ∀ K' : ℕ, 0 ≤ sharingGain P K' := by
    intro K'
    have ha := hP.2.2.2.2.2.1
    unfold sharingGain
    positivity
  -- every AFS equilibrium is bounded by the profit of the best group size
  have hbound : ∀ M', IsAFS M' → ∀ Q', IsEquilibrium Z M' Q' →
      platformProfit Z Q' ≤ PiNS P + sharingGain P K := by
    intro M' hM' Q' hQ'
    refine bound P hP μ Z _ (fun S => ?_) _ M' rfl hM' Q' hQ'
    have : S.card ≤ P.N := by simpa using Finset.card_le_univ S
    linarith [hKmax S.card this]
  obtain ⟨⟨Qs, hQs⟩, hprof⟩ := eq_8_general_K P hP μ Z K hKN
  refine ⟨⟨K, hKfc, ⟨hAFS K, Qs, hQs, fun M' hM' Q' hQ' => ?_⟩, hprof, ?_⟩, ?_⟩
  · rw [hprof Qs hQs]; exact hbound M' hM' Q' hQ'
  · intro Q Q₀ hQ hQ₀
    refine ⟨?_, fun i => ?_⟩
    · rw [hprof Q hQ, ((lemma_1 P hP μ Z).2 Q₀ hQ₀).2]
      linarith [hgain0 K]
    · obtain ⟨h1, h2⟩ := informed_sellers_gain P hP μ Z K hKN Q Q₀ hQ hQ₀
      by_cases hi : (i : ℕ) < K
      · exact (h1 i hi).le
      · exact (h2 i (not_lt.mp hi)).ge
  · intro K' hK'N hopt
    obtain ⟨-, Q', hQ', hQ'max⟩ := hopt
    have hp' := (eq_8_general_K P hP μ Z K' hK'N).2 Q' hQ'
    refine hconv K' hK'N (fun K'' hK'' => ?_)
    obtain ⟨⟨Q'', hQ''⟩, hp''⟩ := eq_8_general_K P hP μ Z K'' hK''
    have := hQ'max _ (hAFS K'') Q'' hQ''
    rw [hp'' Q'' hQ'', hp'] at this
    linarith
