-- Prove2me | solution 1 for SONATA.Push.eq_74
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:32:28.741954+00:00
-- url     : https://prove2.me/submissions/c1ee9542-6ea4-465c-96f7-0e5d28473e13

import Mathlib
import Definitions.Def_SONATA_Push_Network

open SONATA.Push in
theorem solution
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    (∀ ν : ℕ, wavg (φ (ν + 1)) (y (ν + 1)) =
        wavg (φ ν) (y ν) + gradAvg f (x (ν + 1)) - gradAvg f (x ν)) ∧
      ∀ ν : ℕ, wavg (φ ν) (y ν) = gradAvg f (x ν) := by
  obtain ⟨hcl, hdiag, hoff, hcol⟩ := hN.2
  obtain ⟨_, hy0, hφ0, _, hφs, _, hys⟩ := hrun
  have hCnn : ∀ ν i j, 0 ≤ C ν i j := by
    intro ν i j
    by_cases hij : i = j
    · subst hij; linarith [hdiag ν i]
    · by_cases he : Edges ν j i
      · linarith [(hoff ν i j hij).1 he]
      · rw [(hoff ν i j hij).2 he]
  have hφpos : ∀ ν i, 0 < φ ν i := by
    intro ν
    induction ν with
    | zero => intro i; rw [hφ0]; norm_num
    | succ ν ih =>
      intro i
      rw [hφs]
      have h1 : C ν i i * φ ν i ≤ ∑ j, C ν i j * φ ν j :=
        Finset.single_le_sum (f := fun j => C ν i j * φ ν j)
          (fun j _ => mul_nonneg (hCnn ν i j) (ih j).le) (Finset.mem_univ i)
      have h2 : 0 < C ν i i * φ ν i := mul_pos (lt_of_lt_of_le hcl (hdiag ν i)) (ih i)
      linarith
  have part1 : ∀ ν : ℕ, wavg (φ (ν + 1)) (y (ν + 1)) =
      wavg (φ ν) (y ν) + gradAvg f (x (ν + 1)) - gradAvg f (x ν) := by
    intro ν
    unfold wavg gradAvg
    have hstep : ∀ i, φ (ν + 1) i • y (ν + 1) i = ∑ j, C ν i j •
        (φ ν j • y ν j + gradient (f j) (x (ν + 1) j) - gradient (f j) (x ν j)) := by
      intro i
      rw [hys, smul_smul, mul_inv_cancel₀ (hφpos (ν + 1) i).ne', one_smul]
    simp_rw [hstep]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcol, one_smul]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, smul_sub, smul_add]
  refine ⟨part1, ?_⟩
  intro ν
  induction ν with
  | zero =>
    unfold wavg gradAvg
    simp_rw [hφ0, one_smul, hy0]
  | succ ν ih =>
    rw [part1, ih]
    abel
