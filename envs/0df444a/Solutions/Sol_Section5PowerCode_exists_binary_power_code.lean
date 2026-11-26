-- Prove2me | solution 1 for Section5PowerCode.exists_binary_power_code
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:46.263808+00:00
-- url     : https://prove2.me/submissions/39124c77-0184-42ea-8813-b2bd65d17ad1

import Definitions.Def_Section5Verified_Section5BinaryPowerCode
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5PowerCode_codeSign_product_sum_zero
import Theorems.Thm_Section5PowerCode_exists_binary_field_character
import Theorems.Thm_Section5SignMoments_polynomial_mean_match
section
set_option autoImplicit false

namespace Section5PowerCode



theorem binary_field_card {r : ℕ} (hr : r ≠ 0) :
    Fintype.card (GaloisField 2 r)=2^r := by
  rw [Fintype.card_eq_nat_card,GaloisField.card 2 r hr]





end Section5PowerCode

end
section
set_option autoImplicit false

/-! Uniform seed characters of a finite-field power code. Every nonempty
product of at most `k` distinct output signs has exactly zero mean. -/

namespace Section5PowerCode

variable {F : Type*} [Field F] [Fintype F]









theorem codeSign_sq [CharP F 2] {ι : Type*} {k : ℕ}
    (χ : AddChar F ℝ) (v : ι → F) (t : Fin k → F) (i : ι) :
    codeSign χ v t i ^ 2=1 := by
  rw [codeSign,pow_two,← AddChar.map_add_eq_mul,CharTwo.add_self_eq_zero,
    AddChar.map_zero_eq_one]





end Section5PowerCode

end
section
set_option autoImplicit false

namespace Section5PowerCode

variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]

theorem codeSign_squarefree_mean {k : ℕ} (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (S : Finset ι) (hS : S.card ≤ k) :
    Section5SignMoments.mean (fun t : Fin k → F => ∏ i ∈ S, codeSign χ v t i)=
      if S=∅ then 1 else 0 := by
  by_cases he : S=∅
  · subst S
    simp [Section5SignMoments.mean]
  · rw [if_neg he]
    unfold Section5SignMoments.mean
    rw [codeSign_product_sum_zero χ hχ v hv S (Finset.nonempty_iff_ne_empty.mpr he) hS,
      mul_zero]

theorem codeSign_polynomial_mean {k : ℕ} (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v)
    (p : MvPolynomial ι ℝ) (hp : p.totalDegree ≤ k) :
    Section5SignMoments.mean (fun t : Fin k → F => MvPolynomial.eval (codeSign χ v t) p)=
      Section5SignMoments.mean (fun x : ι → Bool =>
        MvPolynomial.eval (Section5BooleanFrame.sign x) p) := by
  exact Section5SignMoments.polynomial_mean_match _
    (fun t i => codeSign_sq χ v t i) k (codeSign_squarefree_mean χ hχ v hv) p hp









end Section5PowerCode

end
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
theorem solution {n r : ℕ} (hr : r ≠ 0) (hn : n ≤ 2^r) (k : ℕ) :
    ∃ (χ : AddChar (GaloisField 2 r) ℝ) (v : Fin n ↪ GaloisField 2 r), χ ≠ 0 ∧
      ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ k →
        Section5SignMoments.mean (fun t : Fin k → GaloisField 2 r =>
          MvPolynomial.eval (Section5PowerCode.codeSign χ v t) p)=
        Section5SignMoments.mean (fun x : Fin n → Bool =>
          MvPolynomial.eval (Section5BooleanFrame.sign x) p) := by
  classical
  obtain ⟨χ,hχ⟩ := Section5PowerCode.exists_binary_field_character (F := GaloisField 2 r)
  have hcard : Fintype.card (Fin n) ≤ Fintype.card (GaloisField 2 r) := by
    simpa only [Fintype.card_fin,Section5PowerCode.binary_field_card hr] using hn
  let v : Fin n ↪ GaloisField 2 r :=
    (Fin.castLEEmb (by simpa only [Fintype.card_fin] using hcard)).trans
      (Fintype.equivFin (GaloisField 2 r)).symm.toEmbedding
  exact ⟨χ,v,hχ,fun p hp => Section5PowerCode.codeSign_polynomial_mean χ hχ v v.injective p hp⟩
