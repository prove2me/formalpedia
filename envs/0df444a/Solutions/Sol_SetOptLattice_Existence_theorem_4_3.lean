-- Prove2me | solution 1 for SetOptLattice.Existence.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:11:59.922453+00:00
-- url     : https://prove2.me/submissions/09ffc1ba-d9a5-42e9-b8b7-01c156733e5a

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model
import Theorems.Thm_SetOptLattice_Existence_proposition_4_1
import Theorems.Thm_SetOptLattice_Existence_remark_3_3
import Theorems.Thm_SetOptLattice_Existence_lemma_2_4

open Set Filter Topology
open scoped Pointwise
open SetOptLattice.Existence

theorem solution {X Z : Type*} [Preorder Z]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X]
    (Ψ : Set (Z → EReal)) (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (hΨne : Ψ.Nonempty)
    (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x))
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hcpt : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → IsCompact (MinPlusSet Ψ f ε)) :
    ((MinPlusSet Ψ f 0).Nonempty ∧ IsCompact (MinPlusSet Ψ f 0) ∧
        HausdorffConverges (MinPlusSet Ψ f) (MinPlusSet Ψ f 0)) ∧
      ((∀ ψ ∈ Ψ, LowerSemicontinuous (fun x => infExt ψ (f x))) →
        (MinSet Ψ f 0).Nonempty ∧ IsSolution Ψ f 0 (MinSet Ψ f 0)) := by
  classical
  -- ψ△(inf f[M]) = inf_{x ∈ M} ψ△(f x)  (Lemma 2.4)
  have hinfM : ∀ (M : Set X), ∀ ψ ∈ Ψ,
      infExt ψ (infImage Ψ f M) = ⨅ x ∈ M, infExt ψ (f x) := by
    intro M ψ hψ
    unfold infImage
    rw [lemma_2_4 Ψ hΨ (f '' M) (by rintro _ ⟨x, -, rfl⟩; exact hf x) ψ hψ, iInf_image]
  have hinf : ∀ ψ ∈ Ψ, infExt ψ (infImage Ψ f univ) = ⨅ x, infExt ψ (f x) := by
    intro ψ hψ
    rw [hinfM univ ψ hψ]
    simp
  -- elementary facts about `epsBound`
  have hlt : ∀ (a : EReal) (ε : ℝ), 0 < ε → a ≠ ⊤ → a < epsBound a ε := by
    intro a ε hε ha
    induction a using EReal.rec with
    | bot => simp [epsBound, hε.ne']
    | coe x =>
      simp only [epsBound, EReal.coe_ne_bot, if_false]
      rw [← EReal.coe_add]
      exact_mod_cast (by linarith : x < x + ε)
    | top => exact absurd rfl ha
  have hreal : ∀ (a : EReal) (ε : ℝ), 0 < ε → a ≠ ⊤ → ∃ r : ℝ, epsBound a ε = (r : EReal) := by
    intro a ε hε ha
    induction a using EReal.rec with
    | bot => exact ⟨-1 / ε, by simp [epsBound, hε.ne']⟩
    | coe x => exact ⟨x + ε, by simp [epsBound]⟩
    | top => exact absurd rfl ha
  have heps0 : ∀ b : EReal, epsBound b 0 = b := by
    intro b
    unfold epsBound
    by_cases h : b = ⊥
    · simp [h]
    · simp [h]
  obtain ⟨hmono, hMinPlus, -, -, hA0⟩ := remark_3_3 Ψ hΨ f hf
  -- (ε, Ψ)-minimizers exist for ε > 0
  have hMinNe : ∀ ε : ℝ, 0 < ε → (MinSet Ψ f ε).Nonempty := by
    intro ε hε
    obtain ⟨ψ, hψ⟩ := hΨne
    by_cases htop : (⨅ x, infExt ψ (f x)) = ⊤
    · refine ⟨0, ψ, hψ, ?_⟩
      have h0 : infExt ψ (f 0) = ⊤ := by rw [iInf_eq_top] at htop; exact htop 0
      rw [hinf ψ hψ, htop, h0]
      simp [epsBound]
    · obtain ⟨x, hx⟩ := iInf_lt_iff.mp (hlt _ ε hε htop)
      exact ⟨x, ψ, hψ, by rw [hinf ψ hψ]; exact hx.le⟩
  set A := MinPlusSet Ψ f with hAdef
  let ι := {ε : ℝ // 0 < ε ∧ ε ≤ ε₀}
  have hιne : Nonempty ι := ⟨⟨ε₀, hε₀, le_rfl⟩⟩
  have hAne : ∀ t : ι, (A t.1).Nonempty := fun t =>
    (hMinNe t.1 t.2.1).mono (hMinPlus t.1 t.2.1.le)
  have hAc : ∀ t : ι, IsCompact (A t.1) := fun t => hcpt t.1 t.2.1 t.2.2
  have hAcl : ∀ t : ι, IsClosed (A t.1) := fun t => (hAc t).isClosed
  have hdir : Directed (· ⊇ ·) (fun t : ι => A t.1) := by
    intro a b
    have hm : 0 < min a.1 b.1 := lt_min a.2.1 b.2.1
    refine ⟨⟨min a.1 b.1, hm, (min_le_left _ _).trans a.2.2⟩, ?_, ?_⟩
    · exact (hmono _ _ hm.le (min_le_left _ _)).2
    · exact (hmono _ _ hm.le (min_le_right _ _)).2
  have hA0eq : A 0 = ⋂ t : ι, A t.1 := by
    rw [hA0]
    ext x
    simp only [mem_iInter]
    constructor
    · intro h t
      exact h t.1 t.2.1
    · intro h ε hε
      have hm : 0 < min ε ε₀ := lt_min hε hε₀
      exact (hmono _ _ hm.le (min_le_left _ _)).2 (h ⟨min ε ε₀, hm, min_le_right _ _⟩)
  have hA0closed : IsClosed (A 0) := by
    rw [hA0eq]; exact isClosed_iInter hAcl
  have hA0sub : ∀ ε : ℝ, 0 < ε → A 0 ⊆ A ε := fun ε hε => (hmono 0 ε le_rfl hε.le).2
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- non-emptiness (Cantor's intersection theorem)
    rw [hA0eq]
    exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ hdir hAne hAc hAcl
  · -- compactness
    exact (hcpt ε₀ hε₀ le_rfl).of_isClosed_subset hA0closed (hA0sub ε₀ hε₀)
  · -- Hausdorff convergence
    intro U hU
    set V := A 0 + interior U with hV
    have hVo : IsOpen V := IsOpen.add_left isOpen_interior
    have hA0V : A 0 ⊆ V := fun x hx => by
      have := Set.add_mem_add hx (mem_interior_iff_mem_nhds.mpr hU)
      simpa using this
    have hVU : V ⊆ A 0 + U := Set.add_subset_add_left interior_subset
    have hempty : (A ε₀ ∩ ⋂ t : ι, (A t.1 ∩ Vᶜ)) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨-, hx⟩
      rw [mem_iInter] at hx
      have hxA0 : x ∈ A 0 := by
        rw [hA0eq, mem_iInter]
        exact fun t => (hx t).1
      exact (hx ⟨ε₀, hε₀, le_rfl⟩).2 (hA0V hxA0)
    have hdir' : Directed (· ⊇ ·) (fun t : ι => A t.1 ∩ Vᶜ) := by
      intro a b
      obtain ⟨c, hca, hcb⟩ := hdir a b
      exact ⟨c, inter_subset_inter_left _ hca, inter_subset_inter_left _ hcb⟩
    obtain ⟨t, ht⟩ := (hcpt ε₀ hε₀ le_rfl).elim_directed_family_closed
      (fun t : ι => A t.1 ∩ Vᶜ) (fun t => (hAcl t).inter hVo.isClosed_compl) hempty hdir'
    have hAtV : A t.1 ⊆ V := by
      intro x hx
      by_contra hxV
      have hx0 : x ∈ A ε₀ := (hmono _ _ t.2.1.le t.2.2).2 hx
      have hmem : x ∈ A ε₀ ∩ (A t.1 ∩ Vᶜ) := ⟨hx0, hx, hxV⟩
      rw [ht] at hmem
      exact hmem
    filter_upwards [Ioo_mem_nhdsGT t.2.1] with ε hε
    refine ⟨fun x hx => hVU (hAtV ((hmono _ _ hε.1.le hε.2.le).2 hx)), fun x hx => ?_⟩
    have : x + 0 ∈ A ε + U := Set.add_mem_add (hA0sub ε hε.1 hx) (mem_of_mem_nhds hU)
    simpa using this
  · -- second part: exact minimizers under lower semicontinuity
    intro hlsc
    have hattain : ∀ ψ ∈ Ψ, ∃ x, infExt ψ (f x) = ⨅ y, infExt ψ (f y) := by
      intro ψ hψ
      by_cases htop : (⨅ x, infExt ψ (f x)) = ⊤
      · refine ⟨0, ?_⟩
        rw [htop]
        rw [iInf_eq_top] at htop
        exact htop 0
      · obtain ⟨rbar, hrbar⟩ := hreal _ ε₀ hε₀ htop
        have hltr := hlt _ ε₀ hε₀ htop
        rw [hrbar] at hltr
        refine proposition_4_1 (fun x => infExt ψ (f x)) rbar hltr ?_
        intro r _ hr
        have hclosed : IsClosed (sublevel (fun x => infExt ψ (f x)) r) :=
          (hlsc ψ hψ).isClosed_preimage (r : EReal)
        refine (hcpt ε₀ hε₀ le_rfl).of_isClosed_subset hclosed ?_
        intro x hx
        apply hMinPlus ε₀ hε₀.le
        refine ⟨ψ, hψ, ?_⟩
        rw [hinf ψ hψ, hrbar]
        exact hx.trans (by exact_mod_cast hr)
    have hxmin : ∀ ψ ∈ Ψ, ∀ x, infExt ψ (f x) = ⨅ y, infExt ψ (f y) → x ∈ MinSet Ψ f 0 := by
      intro ψ hψ x hx
      refine ⟨ψ, hψ, ?_⟩
      rw [heps0, hinf ψ hψ, hx]
    have hne : (MinSet Ψ f 0).Nonempty := by
      obtain ⟨ψ, hψ⟩ := hΨne
      obtain ⟨x, hx⟩ := hattain ψ hψ
      exact ⟨x, hxmin ψ hψ x hx⟩
    refine ⟨hne, ⟨hne, fun ψ hψ => ?_⟩, subset_rfl⟩
    obtain ⟨x, hx⟩ := hattain ψ hψ
    rw [heps0, hinfM _ ψ hψ, hinf ψ hψ, ← hx]
    exact biInf_le (fun y => infExt ψ (f y)) (hxmin ψ hψ x hx)
