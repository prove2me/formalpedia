-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_proof_0b250c56ce6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:46.155137+00:00
-- url     : https://prove2.me/submissions/99c30012-d2f0-483e-bcc4-5d72a90c12da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_isPrime_between_not_mem_f98685f45555
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_lt_of_le_height_ae12bb57a9db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_comap_C_eq_bot_4584caeb175e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
theorem _root_.solution : Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hPC
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let Z := PrimeSpectrum.zeroLocus (R := MRing ι O) (P : Set (MRing ι O))
  let Z' := PrimeSpectrum.zeroLocus (R := MRing ι (FractionRing O))
    (genFib P : Set (MRing ι (FractionRing O)))
  let U := {q : Z // q.1.asIdeal.comap (C : O →+* MRing ι O) = ⊥}
  have ltZ : ∀ a b : Z, a < b ↔ a.1.asIdeal < b.1.asIdeal := fun a b =>
    Subtype.coe_lt_coe.symm.trans (PrimeSpectrum.asIdeal_lt_asIdeal _ _).symm
  have ltU : ∀ a b : U, a < b ↔ a.1.1.asIdeal < b.1.1.asIdeal := fun a b =>
    Subtype.coe_lt_coe.symm.trans (ltZ _ _)
  have memZ : ∀ x : PrimeSpectrum (MRing ι O), x ∈ Z ↔ P ≤ x.asIdeal := fun x =>
    PrimeSpectrum.mem_zeroLocus _ _
  let P0 : Z := ⟨⟨P, hP⟩, (memZ _).2 le_rfl⟩
  let PU : U := ⟨P0, hPC⟩

  have hstep : ∀ n : ℕ, ∀ r : Z, ((n + 1 : ℕ) : ℕ∞) ≤ Order.height r →
      ∃ q : U, q.1.1.asIdeal < r.1.asIdeal ∧ (n : ℕ∞) ≤ Order.height q := by
    intro n
    induction n with
    | zero =>
      intro r hr
      obtain ⟨r0, hr0, -⟩ := exists_lt_of_le_height hr
      exact ⟨PU, lt_of_le_of_lt ((memZ _).1 r0.2) ((ltZ _ _).1 hr0), by simp⟩
    | succ n ih =>
      intro r hr
      obtain ⟨r', hr'r, hr'⟩ := exists_lt_of_le_height hr
      obtain ⟨q, hqr', hq⟩ := ih r' hr'
      have hx : (C ϖ : MRing ι O) ∉ q.1.1.asIdeal := fun h => hϖ.ne_zero (by
        have : ϖ ∈ q.1.1.asIdeal.comap (C : O →+* MRing ι O) := h
        rw [q.2] at this
        exact (Submodule.mem_bot _).1 this)
      obtain ⟨q', hq'p, hqq', hq'r, hq'x⟩ :=
        exists_isPrime_between_not_mem hqr' ((ltZ _ _).1 hr'r) hx
      let qZ : Z := ⟨⟨q', hq'p⟩, (memZ _).2 (((memZ _).1 q.1.2).trans hqq'.le)⟩
      let qU : U := ⟨qZ, comap_C_eq_bot hϖ q' hq'x⟩
      refine ⟨qU, hq'r, ?_⟩
      have hlt : q < qU := (ltU _ _).2 hqq'
      calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ Order.height q + 1 := add_le_add hq le_rfl
        _ ≤ Order.height qU := Order.height_add_one_le hlt
  have hbound : ∀ r : Z, Order.height r ≤ (⨆ q : U, Order.height q) + 1 := by
    intro r
    refine ENat.forall_natCast_le_iff_le.1 fun m hm => ?_
    cases m with
    | zero => simp
    | succ m =>
      obtain ⟨q, -, hq⟩ := hstep m r hm
      push_cast
      exact add_le_add (hq.trans (le_iSup (fun q : U => Order.height q) q)) le_rfl

  have hdisj : ∀ q : U, Disjoint (M : Set (MRing ι O)) (q.1.1.asIdeal : Set (MRing ι O)) := by
    intro q
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ q.1.1.asIdeal.comap (C : O →+* MRing ι O) := hmem
    rw [q.2] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  let Φ : U → Z' := fun q =>
    ⟨⟨q.1.1.asIdeal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))),
      IsLocalization.isPrime_of_isPrime_disjoint M _ _ q.1.1.2 (hdisj q)⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact Ideal.map_mono ((memZ _).1 q.1.2)⟩
  have hΦ : StrictMono Φ := by
    intro a b hab
    rw [ltU] at hab
    refine Subtype.coe_lt_coe.1 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 ?_)
    refine lt_of_le_of_ne (Ideal.map_mono hab.le) fun h => hab.ne ?_
    have ha := IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O))
      a.1.1.2 (hdisj a)
    have hb := IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O))
      b.1.1.2 (hdisj b)
    rw [← ha, ← hb]
    exact congrArg (Ideal.comap _) h
  have : Nonempty Z := ⟨P0⟩
  have : Nonempty U := ⟨PU⟩
  calc Order.krullDim Z = ((⨆ r : Z, Order.height r : ℕ∞) : WithBot ℕ∞) :=
        Order.krullDim_eq_iSup_height_of_nonempty
    _ ≤ (((⨆ q : U, Order.height q) + 1 : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.2 (iSup_le hbound)
    _ = Order.krullDim U + 1 := by
        rw [Order.krullDim_eq_iSup_height_of_nonempty (α := U)]; rfl
    _ ≤ Order.krullDim Z' + 1 := add_le_add (Order.krullDim_le_of_strictMono Φ hΦ) le_rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
