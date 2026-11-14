-- Prove2me | solution 1 for RamanujanPetersson.gamma1_coeff_eq_sum_eigenform_shifts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T06:34:11.293494+00:00
-- url     : https://prove2.me/submissions/e15ac73c-11a3-4096-b01a-f92c4114324b

import Mathlib
import Definitions.Def_RPLib_S1_Decomposition
import Definitions.Def_RPLib_S1_LiUnit
open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

set_option autoImplicit false


theorem solution (M : ℕ) (hM : 0 < M) (k : ℤ) (hk : 1 ≤ k)
    (g : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ (r : ℕ) (c : Fin r → ℂ) (d L : Fin r → ℕ) (χ : (i : Fin r) → DirichletCharacter ℂ (L i))
      (F : (i : Fin r) → CuspForm ((CongruenceSubgroup.Gamma1 (L i) : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k),
      (∀ i, 0 < d i ∧ 0 < L i ∧ d i * L i ∣ M) ∧
      (∀ i, ∀ γ ∈ CongruenceSubgroup.Gamma0 (L i),
        (⇑(F i) ∣[k] γ) = χ i ((γ 1 1 : ℤ) : ZMod (L i)) • ⇑(F i)) ∧
      (∀ i, (qExpansion 1 (F i)).coeff 1 = 1) ∧
      (∀ i, ∀ p n : ℕ, p.Prime →
        (qExpansion 1 (F i)).coeff (p * n) =
          (qExpansion 1 (F i)).coeff p * (qExpansion 1 (F i)).coeff n -
            (if p ∣ L i then 0 else
              χ i (p : ZMod (L i)) * (p : ℂ) ^ (k - 1) *
                (if p ∣ n then (qExpansion 1 (F i)).coeff (n / p) else 0))) ∧
      (∀ i, ∀ p : ℕ, p.Prime → p ∣ L i →
        ‖(qExpansion 1 (F i)).coeff p‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2)) ∧
      ∀ n : ℕ, (qExpansion 1 g).coeff n =
        ∑ i, c i * (if d i ∣ n then (qExpansion 1 (F i)).coeff (n / d i) else 0) := by
  obtain ⟨r, c, d, L, χ, F, hdL, hchi, h1, hrec, hNF, hco⟩ :=
    RP.Decomposition.exists_shift_decomp_N2 M hM k g
  refine ⟨r, c, d, L, χ, F, hdL, hchi, h1, hrec, ?_, hco⟩
  intro i p hp hpL
  obtain ⟨_, hF⟩ := hNF i
  haveI : Fact p.Prime := ⟨hp⟩
  exact RP.LiUnit.norm_coeff_prime_le_all hpL hF

