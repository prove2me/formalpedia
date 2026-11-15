-- Prove2me | solution 1 for ResultantVNP.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T16:35:32.640076+00:00
-- url     : https://prove2.me/submissions/6f939cbf-42ba-4074-8934-c5cf2e6bbee4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ResultantVNP_permanent_to_charCoeff
import Theorems.Thm_ResultantVNP_permanent_vnp_complete

open ResultantVNP MvPolynomial
open scoped Classical

namespace CoefficientHardness

lemma projection_trans {σ τ υ : Type} {f : MvPolynomial σ ℂ} {g : MvPolynomial τ ℂ}
    {h : MvPolynomial υ ℂ} (hf : IsProjection f g) (hg : IsProjection g h) :
    IsProjection f h := by
  obtain ⟨ρ,hρ⟩ := hf
  obtain ⟨θ,hθ⟩ := hg
  let η : υ → σ ⊕ ℂ := fun v => Sum.elim ρ Sum.inr (θ v)
  refine ⟨η,?_⟩
  rw [← hρ,← hθ,comp_aeval_apply]
  congr 1
  ext v
  simp only [aeval_X]
  dsimp [η]
  cases θ v <;> simp

lemma poly_comp {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun n => f (g n)) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  let c := a*(2*b)^a + a + b*a + f (g 0)
  refine ⟨c,fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    dsimp [c]
    omega
  · have hn1 : 1 ≤ n := by omega
    have hp1 : 1 ≤ n^b := Nat.one_le_pow b n hn1
    have hg' : g n ≤ 2*b*n^b := by
      have := hb n
      nlinarith
    have hp := Nat.pow_le_pow_left hg' a
    rw [mul_pow,← pow_mul] at hp
    have he : b*a ≤ c := by dsimp [c]; omega
    have hpow : n^(b*a) ≤ n^c := Nat.pow_le_pow_right hn1 he
    have hc : a*(2*b)^a + a ≤ c := by dsimp [c]; omega
    have hfn := ha (g n)
    calc
      f (g n) ≤ a*((2*b)^a*n^(b*a)) + a := by nlinarith
      _ = (a*(2*b)^a)*n^(b*a) + a := by ring
      _ ≤ (a*(2*b)^a)*n^c + a := Nat.add_le_add_right (Nat.mul_le_mul_left _ hpow) _
      _ ≤ c*n^c+c := by
        have : a*(2*b)^a ≤ c := by omega
        have := Nat.mul_le_mul_right (n^c) this
        omega

lemma rational_isProjection {σ τ : Type} (f : MvPolynomial σ ℂ) (g : MvPolynomial τ ℂ)
    (h : ∃ ρ : τ → σ ⊕ ℚ,
      MvPolynomial.aeval (fun v => Sum.elim X (fun q : ℚ => C (q : ℂ)) (ρ v)) g = f) :
    IsProjection f g := by
  obtain ⟨ρ,hρ⟩ := h
  refine ⟨fun v => Sum.map id (fun q : ℚ => (q : ℂ)) (ρ v),?_⟩
  convert hρ using 1
  congr 1
  ext v
  simp only [aeval_X]
  cases ρ v <;> rfl

end CoefficientHardness

theorem solution (𝓡 : ResultantSystem) :
    IsVNPHardPProj
        (fun m => MvPolynomial.map (Int.castRingHom ℂ) (charCoeff 𝓡 (5 * m ^ 2) (m ^ 2))) 3 ∧
      ∃ t : ℕ → ℕ, PolyBounded t ∧ ∀ n, 1 ≤ n → 3 ≤ t n ∧
        ∃ ρ : Sym (Fin (5 * t n ^ 2)) 3 → (Fin n × Fin n) ⊕ ℚ,
          MvPolynomial.aeval
              (fun T => Sum.elim MvPolynomial.X (fun q : ℚ => MvPolynomial.C (q : ℂ)) (ρ T))
              (MvPolynomial.map (Int.castRingHom ℂ) (charCoeff 𝓡 (5 * t n ^ 2) (t n ^ 2))) =
            (Matrix.of fun i j : Fin n =>
              (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ)).permanent := by
  have hp := ResultantVNP.permanent_to_charCoeff 𝓡
  refine ⟨?_,hp⟩
  obtain ⟨t,ht,htp⟩ := hp
  intro f hf
  obtain ⟨s,hs,hsp⟩ := ResultantVNP.permanent_vnp_complete f hf
  refine ⟨fun n => t (s n),CoefficientHardness.poly_comp ht hs,fun n => ?_⟩
  obtain ⟨hn,hproj⟩ := hsp n
  obtain ⟨htn,hρ⟩ := htp (s n) hn
  exact ⟨htn,CoefficientHardness.projection_trans hproj
    (CoefficientHardness.rational_isProjection _ _ hρ)⟩

#print axioms solution
