-- Prove2me | solution 1 for OpenPitMIP.UltPit.exists_optimal
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:30:02.668594+00:00
-- url     : https://prove2.me/submissions/1582ee58-d4ff-430f-8e5a-8dd20d461a70

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

set_option autoImplicit false
open OpenPitMIP.UltPit PCPSPC

theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : Integrality)
    (hfeas : ∃ x y, I.Feasible κ x y) :
    ∃ x y, I.Optimal κ x y := by
  classical
  let S : Set ((C → Fin T → ℝ) × (B → D → Fin T → ℝ)) := {p | I.Feasible κ p.1 p.2}
  have hcum : ∀ (c : C) (t : Fin T), Continuous (fun p : (C → Fin T → ℝ) × (B → D → Fin T → ℝ) =>
      cum p.1 c t) := by
    intro c t
    unfold cum
    exact continuous_finsetSum _ (fun t' _ =>
      ((continuous_apply t').comp ((continuous_apply c).comp continuous_fst)))
  have hcx : ∀ (c : C) (t : Fin T), Continuous (fun p : (C → Fin T → ℝ) × (B → D → Fin T → ℝ) =>
      p.1 c t) := fun c t => (continuous_apply t).comp ((continuous_apply c).comp continuous_fst)
  have hcy : ∀ (b : B) (d : D) (t : Fin T), Continuous
      (fun p : (C → Fin T → ℝ) × (B → D → Fin T → ℝ) => p.2 b d t) := fun b d t =>
    (continuous_apply t).comp ((continuous_apply d).comp ((continuous_apply b).comp continuous_snd))
  have hclosed : IsClosed S := by
    obtain ⟨Int, hIntC, hInt⟩ : ∃ Int : Set ((C → Fin T → ℝ) × (B → D → Fin T → ℝ)),
        IsClosed Int ∧ ∀ p : (C → Fin T → ℝ) × (B → D → Fin T → ℝ),
          I.IntegralityHolds κ p.1 ↔ p ∈ Int := by
      cases κ
      · refine ⟨⋂ c, ⋂ t, {p | p.1 c t = 0} ∪ {p | p.1 c t = 1}, ?_, ?_⟩
        · exact isClosed_iInter fun c => isClosed_iInter fun t =>
            IsClosed.union (isClosed_eq (hcx c t) continuous_const)
              (isClosed_eq (hcx c t) continuous_const)
        · intro p; simp [IntegralityHolds]
      · refine ⟨⋂ c, ⋂ c', ⋂ (_ : I.arc c c'), ⋂ t,
          {p | cum p.1 c t ≤ 0} ∪ {p | cum p.1 c' t = 1}, ?_, ?_⟩
        · exact isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_iInter fun _ =>
            isClosed_iInter fun t => IsClosed.union (isClosed_le (hcum c t) continuous_const)
              (isClosed_eq (hcum c' t) continuous_const)
        · intro p; simp [IntegralityHolds, imp_iff_not_or, not_lt]
    have hS : S = ({p : (C → Fin T → ℝ) × (B → D → Fin T → ℝ) | (∀ b t, p.1 (I.clu b) t = ∑ d, p.2 b d t) ∧ (∀ c, ∑ t, p.1 c t ≤ 1) ∧
        (∀ c c', I.arc c c' → ∀ t, cum p.1 c t ≤ cum p.1 c' t) ∧
        (∀ i, ∑ b, ∑ d, ∑ t, I.G i b d t * p.2 b d t ≤ I.g i) ∧
        (∀ b d t, 0 ≤ p.2 b d t)}) ∩ Int := by
      ext p
      simp only [S, Set.mem_ofPred_eq, Feasible, Set.mem_inter_iff, ← hInt]
      tauto
    rw [hS]
    refine IsClosed.inter ?_ hIntC
    simp only [Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))
    · exact isClosed_iInter fun b => isClosed_iInter fun t =>
        isClosed_eq (hcx _ _) (continuous_finsetSum _ fun d _ => hcy b d t)
    · exact isClosed_iInter fun c => isClosed_le (continuous_finsetSum _ fun t _ => hcx c t)
        continuous_const
    · exact isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_iInter fun _ =>
        isClosed_iInter fun t => isClosed_le (hcum c t) (hcum c' t)
    · refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
      exact continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun d _ =>
        continuous_finsetSum _ fun t _ => continuous_const.mul (hcy b d t)
    · exact isClosed_iInter fun b => isClosed_iInter fun d => isClosed_iInter fun t =>
        isClosed_le continuous_const (hcy b d t)
  have hbox : S ⊆ (Set.pi Set.univ fun _ : C => Set.pi Set.univ fun _ : Fin T => Set.Icc (0:ℝ) 1) ×ˢ
      (Set.pi Set.univ fun _ : B => Set.pi Set.univ fun _ : D =>
        Set.pi Set.univ fun _ : Fin T => Set.Icc (0:ℝ) 1) := by
    rintro ⟨x, y⟩ hfe
    obtain ⟨hx, hle, -, -, hy, -⟩ : I.Feasible κ x y := hfe
    have hnn : ∀ c t, 0 ≤ x c t := by
      intro c t
      obtain ⟨b, rfl⟩ := hI.clu_surjective c
      rw [hx]
      exact Finset.sum_nonneg (fun d _ => hy b d t)
    have hx1 : ∀ c t, x c t ≤ 1 := fun c t =>
      (Finset.single_le_sum (fun t' _ => hnn c t') (Finset.mem_univ t)).trans (hle c)
    refine ⟨fun c _ t _ => ⟨hnn c t, hx1 c t⟩, fun b _ d _ t _ => ⟨hy b d t, ?_⟩⟩
    have := Finset.single_le_sum (f := fun d => y b d t) (fun d _ => hy b d t) (Finset.mem_univ d)
    have h2 := hx b t
    exact this.trans (h2 ▸ hx1 _ _)
  have hcompact : IsCompact S := by
    refine IsCompact.of_isClosed_subset ?_ hclosed hbox
    exact (isCompact_univ_pi fun c => isCompact_univ_pi fun t => isCompact_Icc).prod
      (isCompact_univ_pi fun b => isCompact_univ_pi fun d => isCompact_univ_pi fun t => isCompact_Icc)
  have hne : S.Nonempty := by
    obtain ⟨x, y, h⟩ := hfeas
    exact ⟨(x, y), h⟩
  have hcont : Continuous (fun p : (C → Fin T → ℝ) × (B → D → Fin T → ℝ) => I.objective p.2) := by
    unfold PCPSPC.objective
    exact continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun d _ =>
      continuous_finsetSum _ fun t _ => continuous_const.mul (hcy b d t)
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  refine ⟨p.1, p.2, hp, fun x' y' h => ?_⟩
  exact hmax (show (x', y') ∈ S from h)
