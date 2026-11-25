-- Prove2me | solution 1 for PI.SqPairLocal.splitPlace_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:13.476249+00:00
-- url     : https://prove2.me/submissions/cf9fad90-a31b-404b-80d4-a491bb9d1179

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SplitPlaceOf
import Theorems.Thm_PI_SqPairLocal_good_scal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Matrix
namespace PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
private lemma pres_integer_smul_one {L : Submodule (𝓞 E) (Fin N → E)} (ε : 𝓞 E) :
    Pres L ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by
  unfold Pres
  intro y hy
  have key : ∀ (r : 𝓞 E) (z : Fin N → E), r • z = (r : E) • z := fun r z => rfl
  have he : ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) *ᵥ y = ε • y := by
    rw [key]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [he]
  exact L.smul_mem ε hy
end PI.SqPairLocal
end
end

set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (hP : PowLoc) : SplitPlace := by
  intro E _ _ _ _ N L' L'' _ _ _ Q hQ hne c hc
  have cjcj : ∀ x : 𝓞 E, cj E (cj E x) = x := fun x => by
    apply NumberField.RingOfIntegers.ext
    show star (star (x : E)) = (x : E)
    exact star_star _
  set Q' := Ideal.comap (cj E) Q with hQ'def
  have hsurj : Function.Surjective (cj E) := fun y => ⟨cj E y, cjcj y⟩
  haveI := hQ
  have hQ' : Q'.IsMaximal := Ideal.comap_isMaximal_of_surjective (cj E) hsurj
  have hcc : Ideal.comap (cj E) Q' = Q := by
    ext x
    rw [hQ'def, Ideal.mem_comap, Ideal.mem_comap, cjcj]
  have hsup : Q ⊔ Q' = ⊤ := by
    by_contra h
    have h1 : Q = Q ⊔ Q' := hQ.eq_of_le h le_sup_left
    have h2 : Q' = Q ⊔ Q' := hQ'.eq_of_le h le_sup_right
    exact hne (h2.trans h1.symm)
  obtain ⟨K, hK⟩ := hP E Q hQ c hc
  obtain ⟨K', hK'⟩ := hP E Q' hQ' c hc
  set M := max K K'
  have h1top : (1 : 𝓞 E) ∈ Q ^ M ⊔ Q' ^ M := by
    rw [Ideal.pow_sup_pow_eq_top hsup]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1top
  have hb1 : b - 1 ∈ Q ^ M := by
    have hba : b - 1 = -a := by
      rw [← hab]
      ring
    rw [hba]
    exact (Q ^ M).neg_mem ha
  have toQ' : ∀ x, x ∈ Q ^ M → cj E x ∈ Q' ^ M := fun x hx => by
    have hle : Q ^ M ≤ Ideal.comap (cj E) (Q' ^ M) := by
      calc Q ^ M = (Ideal.comap (cj E) Q') ^ M := by rw [hcc]
        _ ≤ Ideal.comap (cj E) (Q' ^ M) := Ideal.le_comap_pow _ M
    exact Ideal.mem_comap.mp (hle hx)
  have toQ : ∀ x, x ∈ Q' ^ M → cj E x ∈ Q ^ M := fun x hx => by
    have hle : Q' ^ M ≤ Ideal.comap (cj E) (Q ^ M) := Ideal.le_comap_pow _ M
    exact Ideal.mem_comap.mp (hle hx)
  have hcb1 : cj E b - 1 ∈ Q' ^ M := by
    have h := toQ' _ hb1
    rwa [map_sub, map_one] at h
  have hcb : cj E b ∈ Q ^ M := toQ _ hb
  have dvQ : ∀ x, x ∈ Q ^ M → Dv Q c x := fun x hx =>
    hK x (Ideal.pow_le_pow_right (le_max_left K K') hx)
  have dvQ' : ∀ x, x ∈ Q' ^ M → Dv Q' c x := fun x hx =>
    hK' x (Ideal.pow_le_pow_right (le_max_right K K') hx)
  haveI := hQ.isPrime
  haveI := hQ'.isPrime
  refine ⟨(b : E) • (1 : Matrix (Fin N) (Fin N) E), pres_integer_smul_one b, pres_integer_smul_one b, ?_, ?_⟩
  · apply good_scal
    · exact dvQ _ (Ideal.mul_mem_left _ b hb1)
    · have hr : b + cj E b - 1 = (b - 1) + cj E b := by ring
      rw [hr]
      exact dvQ _ (Ideal.add_mem _ hb1 hcb)
  · apply good_scal
    · exact dvQ' _ (Ideal.mul_mem_right _ _ hb)
    · have hr : b + cj E b - 1 = b + (cj E b - 1) := by ring
      rw [hr]
      exact dvQ' _ (Ideal.add_mem _ hb hcb1)
end PI.SqPairLocal
