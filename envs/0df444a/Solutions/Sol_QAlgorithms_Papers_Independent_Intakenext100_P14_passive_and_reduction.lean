-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P14.passive_and_reduction
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T10:19:52.280035+00:00
-- url     : https://prove2.me/submissions/f2d4ee01-e43f-4bb4-879d-d9e41483475b

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P14

noncomputable section

open QAlgorithms.Papers.Independent.Intakenext100.P14

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Gap48.P11 (blockMatrix cqDistance)

open QAlgorithms.Papers.Independent.Claimed50.P31 (bb84Vector)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Positive list length and inhabited fibers supply the tagged union's inhabitant.
This derived instance adds no hypothesis to Lemma 2.2. -/
local instance {m : ℕ} [NeZero m] {A : Fin m → Type*}
    [∀ i, Nonempty (A i)] : Nonempty (Sigma A) :=
  ⟨⟨0, Classical.choice (inferInstance : Nonempty (A 0))⟩⟩

namespace Prove2MeS03.P003

/-- The full block-diagonal view has zero distance from itself. -/
theorem cqDistance_self {E : Type*} [Fintype E]
    (R : Bool → Matrix E E ℂ) : cqDistance R R = 0 := by
  classical
  simp [cqDistance, QAlgorithms.traceDistance, QAlgorithms.traceNorm, cfc_zero]

end Prove2MeS03.P003

/-- PDF p.3, unnumbered passive AND reduction. Both parties receive the
identification decision. Correctness and full-view privacy are preserved for
the prescribed maps; no malicious-security claim is made. -/
theorem solution
    {W EA EB : Type*} [Fintype EA] [Fintype EB]
    (P : PassiveExecution W EA EB) (wzero wzeroOther wone : W)
    (hzero : wzero ≠ wzeroOther) (hleft : wzero ≠ wone)
    (hright : wzeroOther ≠ wone) (delta epsilon : ℝ)
    (hsecurity : PassiveEqualitySecurity P delta epsilon) :
    (∀ a b : Bool,
      blockMass (P.bob (andPassword wzero wone a)
        (andPassword wzeroOther wone b)) (a && b) ≥ 1 - delta ∧
      ∀ t, blockMass (P.alice (andPassword wzero wone a)
        (andPassword wzeroOther wone b)) t =
        blockMass (P.bob (andPassword wzero wone a)
          (andPassword wzeroOther wone b)) t) ∧
    (∀ a b c : Bool, (a && b) = (a && c) →
      cqDistance (P.alice (andPassword wzero wone a) (andPassword wzeroOther wone b))
        (P.alice (andPassword wzero wone a) (andPassword wzeroOther wone c)) ≤ epsilon) ∧
    (∀ b a c : Bool, (a && b) = (c && b) →
      cqDistance (P.bob (andPassword wzero wone a) (andPassword wzeroOther wone b))
        (P.bob (andPassword wzero wone c) (andPassword wzeroOther wone b)) ≤ epsilon)  := by
  rcases hsecurity with ⟨hdelta, hepsilon, hcorrect, halice, hbob⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have hc := hcorrect (andPassword wzero wone a) (andPassword wzeroOther wone b)
    constructor
    · cases a <;> cases b <;>
        simpa [andPassword, hzero, hleft, Ne.symm hright] using hc.2.2.2
    · exact hc.2.2.1
  · intro a b c hout
    cases a
    · apply halice
      · cases b <;> simp [andPassword, Ne.symm hzero, Ne.symm hleft]
      · cases c <;> simp [andPassword, Ne.symm hzero, Ne.symm hleft]
    · have hbc : b = c := by simpa using hout
      subst c
      rw [Prove2MeS03.P003.cqDistance_self]
      exact hepsilon
  · intro b a c hout
    cases b
    · apply hbob
      · cases a <;> simp [andPassword, hzero, Ne.symm hright]
      · cases c <;> simp [andPassword, hzero, Ne.symm hright]
    · have hac : a = c := by simpa using hout
      subst c
      rw [Prove2MeS03.P003.cqDistance_self]
      exact hepsilon
#print axioms solution

end
