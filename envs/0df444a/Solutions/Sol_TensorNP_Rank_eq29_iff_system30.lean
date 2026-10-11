-- Prove2me | solution 1 for TensorNP.Rank.eq29_iff_system30
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:44:32.41525+00:00
-- url     : https://prove2.me/submissions/211cc0ae-e588-438f-9649-5c1b8eca68f4

import Definitions.Def_TensorNP_Rank_Defs
import Definitions.Def_TensorNP_Rank_Construction
import Mathlib

open TensorNP.Rank

private theorem rank_decompositions_nonempty {E : Type} [Field E] {l m n : ℕ}
    (B : Fin l → Fin m → Fin n → E) :
    {r : ℕ | ∃ (lam : Fin r → E) (x : Fin r → Fin l → E)
      (y : Fin r → Fin m → E) (z : Fin r → Fin n → E),
      B = ∑ s, lam s • outer (x s) (y s) (z s)}.Nonempty := by
  classical
  let I := Fin l × Fin m × Fin n
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, (fun s => B (e s).1 (e s).2.1 (e s).2.2),
    (fun s => Pi.single (e s).1 1), (fun s => Pi.single (e s).2.1 1),
    (fun s => Pi.single (e s).2.2 1), ?_⟩
  rw [e.sum_comp (fun s : I => B s.1 s.2.1 s.2.2 •
    outer (Pi.single s.1 1) (Pi.single s.2.1 1) (Pi.single s.2.2 1))]
  ext i j k
  change B i j k = (∑ s : Fin l × Fin m × Fin n, B s.1 s.2.1 s.2.2 •
    outer (Pi.single s.1 1) (Pi.single s.2.1 1) (Pi.single s.2.2 1)) i j k
  simp [outer, Pi.single_apply, Fintype.sum_prod_type, Finset.sum_apply]

theorem solution :
    (∀ {E : Type} [Field E] {l m n : ℕ} (B : Fin l → Fin m → Fin n → E),
      rankOver E B ≤ 2 →
        ∃ (u₁ v₁ : Fin l → E) (u₂ v₂ : Fin m → E) (u₃ v₃ : Fin n → E),
          B = outer u₁ u₂ u₃ + outer v₁ v₂ v₃) ∧
    (∀ {K : Type} [Field K] [CharZero K] (u₁ u₂ u₃ v₁ v₂ v₃ : Fin 2 → K),
      ((fun i j k => (tensorA i j k : K)) = outer u₁ u₂ u₃ + outer v₁ v₂ v₃ ↔
        System30 (u₁ 0) (u₂ 0) (u₃ 0) (u₁ 1) (u₂ 1) (u₃ 1)
          (v₁ 0) (v₂ 0) (v₃ 0) (v₁ 1) (v₂ 1) (v₃ 1))) := by
  constructor
  · intro E _ l m n B hRank
    have hmem := Nat.sInf_mem (rank_decompositions_nonempty B)
    change ∃ (lam : Fin (rankOver E B) → E) (x : Fin (rankOver E B) → Fin l → E)
      (y : Fin (rankOver E B) → Fin m → E) (z : Fin (rankOver E B) → Fin n → E),
      B = ∑ s, lam s • outer (x s) (y s) (z s) at hmem
    obtain ⟨r, hr, lam, x, y, z, hB⟩ :
        ∃ r ≤ 2, ∃ (lam : Fin r → E) (x : Fin r → Fin l → E)
          (y : Fin r → Fin m → E) (z : Fin r → Fin n → E),
          B = ∑ s, lam s • outer (x s) (y s) (z s) :=
      ⟨rankOver E B, hRank, hmem⟩
    interval_cases r
    · refine ⟨0, 0, 0, 0, 0, 0, ?_⟩
      ext i j k
      simpa [outer] using congrArg (fun T => T i j k) hB
    · refine ⟨lam 0 • x 0, 0, y 0, 0, z 0, 0, ?_⟩
      ext i j k
      simpa [outer, mul_assoc] using congrArg (fun T => T i j k) hB
    · refine ⟨lam 0 • x 0, lam 1 • x 1, y 0, y 1, z 0, z 1, ?_⟩
      ext i j k
      simpa [Fin.sum_univ_two, outer, mul_assoc] using congrArg (fun T => T i j k) hB
  · intro K _ _ u₁ u₂ u₃ v₁ v₂ v₃
    constructor
    · intro h
      have hh := fun i j k => congrArg (fun T => T i j k) h
      dsimp [System30]
      have h000 := hh 0 0 0
      have h010 := hh 0 1 0
      have h100 := hh 1 0 0
      have h110 := hh 1 1 0
      have h001 := hh 0 0 1
      have h011 := hh 0 1 1
      have h101 := hh 1 0 1
      have h111 := hh 1 1 1
      simp [tensorA, outer, vecX, vecY] at h000 h010 h100 h110 h001 h011 h101 h111
      exact ⟨h000.symm, by simpa [mul_comm, mul_left_comm, mul_assoc] using h010.symm,
        by simpa [mul_comm, mul_left_comm, mul_assoc] using h100.symm,
        by simpa [mul_comm, mul_left_comm, mul_assoc] using h110.symm,
        h001.symm, h011.symm,
        by simpa [mul_comm, mul_left_comm, mul_assoc] using h101.symm, h111.symm⟩
    · rintro ⟨h000, h010, h100, h110, h001, h011, h101, h111⟩
      ext i j k
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp_all [tensorA, outer, vecX, vecY, mul_comm, mul_left_comm, mul_assoc]
