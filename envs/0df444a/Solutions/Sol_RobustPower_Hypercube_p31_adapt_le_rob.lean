-- Prove2me | solution 1 for RobustPower.Hypercube.p31_adapt_le_rob
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:56:01.948546+00:00
-- url     : https://prove2.me/submissions/fe5f1505-5ca8-4264-be64-36f698f00739

import Definitions.Def_RobustPower_Hypercube_Problems

open RobustPower.Hypercube

theorem solution
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (hc : 0 ≤ c) (hd : ∀ ω, 0 ≤ d ω) :
    zAdapt A B b I₁ I₂ c d ≤ zRob A B b I₁ I₂ c d := by
  unfold zAdapt zRob
  refine le_iInf fun x => le_iInf fun y => le_iInf fun hxy => ?_
  have hconstant : adaptFeasible A B b I₁ I₂ x (fun _ => y) :=
    ⟨hxy.1, fun ω => ⟨hxy.2.1, hxy.2.2 ω⟩⟩
  exact iInf_le_of_le x (iInf_le_of_le (fun _ => y) (iInf_le_of_le hconstant le_rfl))
