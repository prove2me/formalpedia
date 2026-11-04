-- Prove2me | solution 1 for SONATA.Undir.theorem_3_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:16:50.073071+00:00
-- url     : https://prove2.me/submissions/a11f45e6-7868-471f-a97f-dd44f8d4a2f6

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting
import Theorems.Thm_SONATA_Push_theorem_4_5

open SONATA.Undir

theorem solution
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    (hcond : Dlmn Dl ≤ mutmn μt) :
    ∃ αbar : ℝ, 0 < αbar ∧ αbar ≤ 1 ∧ ∀ α : ℝ, 0 < α → α < αbar →
      ∀ x y xh : ℕ → Stack m d, IsRun K f G ft W α x y xh →
        ∀ i : Fin m, ∃ C z : ℝ, 0 ≤ z ∧ z < 1 ∧
          ∀ ν : ℕ, |Uobj f G (x ν i) - Uobj f G xstar| ≤ C * z ^ ν := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨1, one_pos, le_rfl, fun _ _ _ _ _ _ _ i => i.elim0⟩
  -- the smooth parts coincide
  have hF : SONATA.Push.Fsum f = Fobj f := by
    funext w; simp [SONATA.Push.Fsum, Fobj, one_div]
  have hU : SONATA.Push.U f G = Uobj f G := by
    funext w; simp [SONATA.Push.U, Uobj, hF]
  -- the constant network
  let i0 : Fin m := ⟨0, hm⟩
  let g : Fin m × Fin m → ℝ := fun p => if 0 < W p.1 p.2 then W p.1 p.2 else 1
  have hne : (Finset.univ : Finset (Fin m × Fin m)).Nonempty := ⟨(i0, i0), Finset.mem_univ _⟩
  let cl : ℝ := Finset.univ.inf' hne g
  have hgpos : ∀ p, 0 < g p := by
    intro p; simp only [g]; split_ifs with h
    · exact h
    · exact one_pos
  have hclpos : 0 < cl := (Finset.lt_inf'_iff hne).2 (fun p _ => hgpos p)
  have hcle : ∀ i j, 0 < W i j → cl ≤ W i j := by
    intro i j h
    have := Finset.inf'_le g (Finset.mem_univ (i, j))
    simpa [g, h] using this
  have hD := hS.D
  have hN : SONATA.Push.NetworkHyp (fun _ a b => Gr.Adj a b) 1 (fun _ => W) cl := by
    refine ⟨⟨one_pos, ?_⟩, ⟨hclpos, ?_, ?_, ?_⟩⟩
    · intro ν i j
      have hr : Relation.ReflTransGen Gr.Adj i j :=
        (SimpleGraph.reachable_iff_reflTransGen i j).1 (hS.B.preconnected i j)
      induction hr with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hab ih => exact ih.tail ⟨ν, by omega, by omega, hab⟩
    · intro ν i; exact hcle i i (hD.diag_pos i)
    · intro ν i j hij
      refine ⟨fun hji => hcle i j (hD.adj_pos i j hij hji.symm), fun hji => ?_⟩
      exact hD.nonadj_zero i j hij (fun h => hji h.symm)
    · intro ν j; exact hD.col_sum j
  have hA := hS.A
  have hC := hS.C
  have hP : SONATA.Push.ProblemHyp K O f G μ L ft μt Lt Dl Du xstar := by
    refine ⟨hm, ?_, ?_, ?_, hS.xstar_mem, ?_⟩
    · refine ⟨hA.K_nonempty, hA.K_closed, hA.K_convex, hA.O_open, hA.K_sub_O,
        fun i => ⟨hA.f_diff i, hA.grad_diff i, hA.f_convex i, hA.f_locConvex i⟩,
        hA.mu_pos, hA.L_pos, ?_, hA.G_convex⟩
      rw [hF]; exact hA.hess_bounds
    · intro i
      exact ⟨hC.smooth i, hC.grad_match i, hC.lipschitz i, hC.mut_pos i, hC.strongly_convex i⟩
    · intro i
      rw [hF]; exact hS.eq15 i
    · rw [hU]; exact hS.xstar_min
  obtain ⟨αbar, h0, h1, hmain⟩ :=
    SONATA.Push.theorem_4_5 K O f G μ L ft μt Lt Dl Du xstar (fun _ a b => Gr.Adj a b) 1
      (fun _ => W) cl hP hN hcond
  refine ⟨αbar, h0, h1, fun α hα0 hα1 x y xh hrun i => ?_⟩
  have hrun' : SONATA.Push.IsRun K f G ft (fun _ => W) α x y xh (fun _ _ => 1) := by
    have hrow : ∀ i, ∑ j, W i j * (1 : ℝ) = 1 := by
      intro i; simpa using hD.row_sum i
    refine ⟨hrun.init_mem, hrun.init_y, fun _ => rfl, fun ν i => ⟨hrun.xh_mem ν i, ?_⟩,
      fun ν i => (hrow i).symm, fun ν i => ?_, fun ν i => ?_⟩
    · exact hrun.xh_min ν i
    · rw [hrun.consensus ν i]
      simp only [inv_one, one_smul, mul_one]
      rfl
    · rw [hrun.tracking ν i]
      simp only [inv_one, one_smul]
  obtain ⟨Cc, z, hz0, hz1, hb⟩ := hmain α hα0 hα1 x y xh (fun _ _ => 1) hrun' i
  refine ⟨Cc, z, hz0, hz1, fun ν => ?_⟩
  have := hb ν
  rwa [hU] at this
