-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_ideal_sum
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T13:45:39.680591+00:00
-- url     : https://prove2.me/submissions/66eb13a2-f9b7-448f-919e-9d92b0df33c8

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension

noncomputable section
open WeierstrassEllipticZeta

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (m n : V → ℕ) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (m v)
    let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    I ⊔ J = (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (min (m v) (n v))) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I ⊔ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I ⊔ J) =
        ∑ v : V, min (m v) (n v) ∧
      (I ⊔ J = ⊤ ↔ ∀ v : V, m v = 0 ∨ n v = 0) := by
  classical
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (m v)
  let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let K : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (min (m v) (n v))
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  have hmono (v : V) (a b : ℕ) (hba : b ≤ a) :
      extensionChartContactIdeal g₂ g₃ c v.val a ≤
        extensionChartContactIdeal g₂ g₃ c v.val b := by
    intro p hp
    exact (hc.1 c v.val b p).mpr fun j hj =>
      (hc.1 c v.val a p).mp hp j (hj.trans_le hba)
  have hsum : I ⊔ J = K := by
    apply le_antisymm
    · apply sup_le
      · intro p hp
        exact (Submodule.mem_iInf _).mpr fun v =>
          hmono v _ _ (min_le_left _ _) ((Submodule.mem_iInf _).mp hp v)
      · intro p hp
        exact (Submodule.mem_iInf _).mpr fun v =>
          hmono v _ _ (min_le_right _ _) ((Submodule.mem_iInf _).mp hp v)
    · intro p hp
      let a : V → MvPolynomial (Fin 4) ℂ := fun v => if m v ≤ n v then p else 0
      obtain ⟨q, hq⟩ := hc.2.2.2.2.2.2 c V (fun v => max (m v) (n v)) a
      have hlocal (v : V) : q ∈ extensionChartContactIdeal g₂ g₃ c v.val (m v) ∧
          p - q ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v) := by
        have hpv := (Submodule.mem_iInf _).mp hp v
        by_cases hmn : m v ≤ n v
        · have hdiff : q - p ∈ extensionChartContactIdeal g₂ g₃ c v.val (max (m v) (n v)) := by
            simpa only [a, if_pos hmn] using hq v
          have hpI : p ∈ extensionChartContactIdeal g₂ g₃ c v.val (m v) := by
            simpa only [min_eq_left hmn] using hpv
          refine ⟨?_, ?_⟩
          · simpa only [sub_add_cancel] using
              (extensionChartContactIdeal g₂ g₃ c v.val (m v)).add_mem
                (hmono v _ _ (le_max_left _ _) hdiff) hpI
          · simpa only [neg_sub] using
              (extensionChartContactIdeal g₂ g₃ c v.val (n v)).neg_mem
                (hmono v _ _ (le_max_right _ _) hdiff)
        · have hqv : q ∈ extensionChartContactIdeal g₂ g₃ c v.val (max (m v) (n v)) := by
            simpa only [a, if_neg hmn, sub_zero] using hq v
          have hpJ : p ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v) := by
            simpa only [min_eq_right (le_of_not_ge hmn)] using hpv
          exact ⟨hmono v _ _ (le_max_left _ _) hqv,
            (extensionChartContactIdeal g₂ g₃ c v.val (n v)).sub_mem hpJ
              (hmono v _ _ (le_max_right _ _) hqv)⟩
      exact Submodule.mem_sup.mpr ⟨q, (Submodule.mem_iInf _).mpr fun v => (hlocal v).1,
        p - q, (Submodule.mem_iInf _).mpr fun v => (hlocal v).2, add_sub_cancel _ _⟩
  obtain ⟨hfinite, hdim, _⟩ :=
    elliptic_extension_contact_quotient_dimension g₂ g₃ c V (fun v => min (m v) (n v))
  refine ⟨hsum, ?_, ?_, ?_⟩
  · change FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I ⊔ J)
    rw [hsum]
    exact hfinite
  · change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I ⊔ J) = _
    rw [hsum]
    exact hdim
  · change I ⊔ J = ⊤ ↔ _
    rw [hsum]
    constructor
    · intro htop v
      by_cases hm : m v = 0
      · exact Or.inl hm
      · refine Or.inr (by_contra fun hn => ?_)
        have hone : (1 : MvPolynomial (Fin 4) ℂ) ∈ K := by rw [htop]; trivial
        have hz := (hc.1 c v.val (min (m v) (n v)) 1).mp
          ((Submodule.mem_iInf _).mp hone v) 0
          (lt_min (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn))
        simp at hz
    · intro hzero
      apply top_unique
      intro p _
      apply (Submodule.mem_iInf _).mpr
      intro v
      have hmin : min (m v) (n v) = 0 := by
        rcases hzero v with hm | hn
        · simp [hm]
        · simp [hn]
      apply (hc.1 c v.val (min (m v) (n v)) p).mpr
      intro j hj
      omega

