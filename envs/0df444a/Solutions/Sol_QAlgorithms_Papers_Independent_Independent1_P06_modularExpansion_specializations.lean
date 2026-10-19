-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.modularExpansion_specializations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:31:12.99101+00:00
-- url     : https://prove2.me/submissions/9112d824-b187-46f2-9497-4aab5ee641b4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P06
/-- Section 7 specializations, PDF p.36. The kernel is ker(G transpose). Positive
cardinalities exclude division by zero in the normalized classical definition. -/
theorem gq_mcw_le {V : Type*} [Fintype V] (W : Submodule F2 (V → F2)) (x w : V → F2) (hw : w ∈ W) :
    modularCosetWeight W x ≤ hammingNorm (x + w) :=
  Finset.inf'_le _ (Finset.mem_univ (⟨w, hw⟩ : W))

theorem gq_mcw_attain {V : Type*} [Fintype V] (W : Submodule F2 (V → F2)) (x : V → F2) :
    ∃ w ∈ W, modularCosetWeight W x = hammingNorm (x + w) := by
  unfold modularCosetWeight
  obtain ⟨w, _, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr ⟨(0 : W)⟩)
    (fun w : W => hammingNorm (x + w.val))
  exact ⟨w.1, w.2, h⟩

theorem gq_mcw_le_card {V : Type*} [Fintype V] (W : Submodule F2 (V → F2)) (x : V → F2) :
    modularCosetWeight W x ≤ Fintype.card V :=
  (gq_mcw_le W x 0 W.zero_mem).trans hammingNorm_le_card_fintype

theorem gq_restrict_univ {V : Type*} [Fintype V] (v : V → F2) : restrictVertices Finset.univ v = v := by
  funext j; simp [restrictVertices]

theorem gq_span_one {V : Type*} [Fintype V] (U : Finset V) (v : V → F2) :
    let o := restrictVertices U (fun _ => (1 : F2))
    addressed (Submodule.span F2 {o}) = U ∧
    (modularCosetWeight (Submodule.span F2 {o}) (restrictVertices U v) : ℝ) =
      min (hammingNorm (restrictVertices U v) : ℝ) ((U.card : ℝ) - hammingNorm (restrictVertices U v)) := by
  intro o
  have hmem : ∀ w, w ∈ Submodule.span F2 {o} ↔ w = 0 ∨ w = o := by
    intro w
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a
      · left; exact zero_smul _ _
      · right; exact one_smul _ _
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hsplit : (hammingNorm (restrictVertices U v) : ℝ) + hammingNorm (restrictVertices U v + o) = U.card := by
    have h1 : hammingNorm (restrictVertices U v) = (U.filter (fun u => v u ≠ 0)).card := by
      unfold hammingNorm; congr 1; ext u; simp [restrictVertices]
    have h2 : hammingNorm (restrictVertices U v + o) = (U.filter (fun u => ¬ v u ≠ 0)).card := by
      unfold hammingNorm; congr 1; ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, restrictVertices, o]
      by_cases hu : u ∈ U
      · simp only [hu, if_true, true_and]
        have : ∀ a : F2, a + 1 ≠ 0 ↔ ¬ a ≠ 0 := by decide
        exact this _
      · simp [hu]
    rw [h1, h2]
    exact_mod_cast Finset.card_filter_add_card_filter_not _
  refine ⟨?_, ?_⟩
  · ext u
    simp only [addressed, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, hwu⟩
      rcases (hmem w).1 hw with rfl | rfl
      · simp at hwu
      · by_contra hu; simp [o, restrictVertices, hu] at hwu
    · intro hu
      exact ⟨o, (hmem o).2 (Or.inr rfl), by simp [o, restrictVertices, hu]⟩
  · apply le_antisymm
    · apply le_min
      · have := gq_mcw_le (Submodule.span F2 {o}) (restrictVertices U v) 0 ((hmem 0).2 (Or.inl rfl))
        rw [add_zero] at this
        exact_mod_cast this
      · have := gq_mcw_le (Submodule.span F2 {o}) (restrictVertices U v) o ((hmem o).2 (Or.inr rfl))
        have h' : (modularCosetWeight (Submodule.span F2 {o}) (restrictVertices U v) : ℝ) ≤
            hammingNorm (restrictVertices U v + o) := by exact_mod_cast this
        linarith
    · obtain ⟨w, hw, hweq⟩ := gq_mcw_attain (Submodule.span F2 {o}) (restrictVertices U v)
      rw [hweq]
      rcases (hmem w).1 hw with rfl | rfl
      · rw [add_zero]; exact min_le_left _ _
      · refine (min_le_right _ _).trans (le_of_eq ?_)
        linarith

theorem solution {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (U : Finset V) (t M rho : ℝ) (omega : ℕ)
    (tpositive : 0 < t) (vertices : 0 < Fintype.card V) (edges : 0 < Fintype.card E)
    (locality : ∀ e, hammingNorm (fun v => G v e) ≤ omega) :
    (HasModularExpansion G (Submodule.span F2 {restrictVertices U (fun _ => 1)}) t M ↔
      HasRelativeExpansion G U t M) ∧
    ((Fintype.card V : ℝ) ≤ t →
      ((HasRelativeExpansion G Finset.univ t M ↔ HasGlobalExpansion G M) ∧
       (addressed (LinearMap.ker G.transpose.mulVecLin) = Finset.univ →
        (HasModularExpansion G (LinearMap.ker G.transpose.mulVecLin) t
          (rho * Fintype.card E / Fintype.card V) ↔ HasClassicalSoundness G omega rho)))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hA, -⟩ := gq_span_one U (fun _ => 0)
    simp only [HasModularExpansion, HasRelativeExpansion]
    rw [hA]
    refine and_congr_right (fun _ => forall_congr' (fun v => ?_))
    rw [(gq_span_one U v).2]
  · intro hV
    refine ⟨?_, ?_⟩
    · simp only [HasRelativeExpansion, HasGlobalExpansion, gq_restrict_univ, Finset.card_univ]
      constructor
      · rintro ⟨-, h⟩ v
        have := h v
        have hle : min (hammingNorm v : ℝ) ((Fintype.card V : ℝ) - hammingNorm v) ≤ t := by
          have : (hammingNorm v : ℝ) ≤ Fintype.card V := by exact_mod_cast hammingNorm_le_card_fintype
          have h0 : (0 : ℝ) ≤ hammingNorm v := by positivity
          exact (min_le_right _ _).trans (by linarith)
        rwa [min_eq_right hle] at this
      · intro h
        refine ⟨tpositive, fun v => ?_⟩
        have hle : min (hammingNorm v : ℝ) ((Fintype.card V : ℝ) - hammingNorm v) ≤ t := by
          have : (hammingNorm v : ℝ) ≤ Fintype.card V := by exact_mod_cast hammingNorm_le_card_fintype
          have h0 : (0 : ℝ) ≤ hammingNorm v := by positivity
          exact (min_le_right _ _).trans (by linarith)
        rw [min_eq_right hle]
        exact h v
    · intro hadd
      simp only [HasModularExpansion, HasClassicalSoundness, hadd, gq_restrict_univ]
      have hE : (0 : ℝ) < Fintype.card E := by exact_mod_cast edges
      have hVp : (0 : ℝ) < Fintype.card V := by exact_mod_cast vertices
      constructor
      · rintro ⟨-, h⟩
        refine ⟨locality, fun v => ?_⟩
        have h1 := h v
        have hle : (modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v : ℝ) ≤ t := by
          have := gq_mcw_le_card (LinearMap.ker G.transpose.mulVecLin) v
          have : (modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v : ℝ) ≤ Fintype.card V := by
            exact_mod_cast this
          linarith
        rw [min_eq_right hle] at h1
        rw [le_div_iff₀ hE]
        calc rho / (Fintype.card V : ℝ) * (modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v : ℝ) *
              Fintype.card E = rho * Fintype.card E / Fintype.card V *
                (modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v : ℝ) := by ring
          _ ≤ _ := h1
      · rintro ⟨-, h⟩
        refine ⟨tpositive, fun v => ?_⟩
        have h1 := h v
        have hle : (modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v : ℝ) ≤ t := by
          have := gq_mcw_le_card (LinearMap.ker G.transpose.mulVecLin) v
          have : (modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v : ℝ) ≤ Fintype.card V := by
            exact_mod_cast this
          linarith
        rw [min_eq_right hle]
        rw [le_div_iff₀ hE] at h1
        calc rho * Fintype.card E / Fintype.card V *
              (modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v : ℝ) =
            rho / (Fintype.card V : ℝ) * (modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v : ℝ) *
              Fintype.card E := by ring
          _ ≤ _ := h1

