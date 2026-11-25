-- Prove2me | solution 1 for PI.ScRefExists.TH.cj_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:32.928276+00:00
-- url     : https://prove2.me/submissions/3c911044-b740-4b33-97cf-113c45e2e52f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Theorems.Thm_PI_ScRefExists_TH_fixed_int
import Theorems.Thm_PI_ScRefExists_TH_mem_cj
import Theorems.Thm_PI_ScRefExists_TH_cj_cj
import Theorems.Thm_PI_ScRefExists_TH_comap_cj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.TH
theorem _root_.solution (g : ℕ) (hg : 1 ≤ g) (hS : PI.ScRefExists.Sk.SplitG I g) (P : HeightOneSpectrum (𝓞 I.E))
    (hP : (g : 𝓞 I.E) ∈ P.asIdeal) : cj I P ≠ P := by
  intro hfix
  have hg0 : (g : 𝓞 I.F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hgv : (g : 𝓞 I.F) ∈ P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hP
  let v : HeightOneSpectrum (𝓞 I.F) :=
    { asIdeal := P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := fun h => hg0 (by rw [h, Ideal.mem_bot] at hgv; exact hgv) }
  have hcard := hS v hgv
  let P' : {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} := ⟨P, rfl⟩
  obtain ⟨x, hx, hxu⟩ := (Nat.card_eq_two_iff' P').mp hcard
  let cx : {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} := ⟨cj I x.1, by rw [comap_cj]; exact x.2⟩
  have hcx : cx ≠ P' := by
    intro h
    apply hx
    apply Subtype.ext
    have h1 : cj I x.1 = P := congrArg Subtype.val h
    rw [← cj_cj I x.1, h1, hfix]
  have hcxx : cj I x.1 = x.1 := congrArg Subtype.val (hxu cx hcx)
  have hne : P.asIdeal ≠ x.1.asIdeal := by
    intro h
    apply hx
    apply Subtype.ext
    exact (HeightOneSpectrum.ext h).symm
  have hnle : ¬ P.asIdeal ≤ x.1.asIdeal := fun h =>
    hne (P.isMaximal.eq_of_le x.1.isPrime.ne_top h)
  obtain ⟨θ, hθP, hθx⟩ := SetLike.not_le_iff_exists.mp hnle
  have hfixy : star ((θ * sg I θ : 𝓞 I.E) : I.E) = ((θ * sg I θ : 𝓞 I.E) : I.E) := by
    show star ((θ : I.E) * (sg I θ : I.E)) = (θ : I.E) * (sg I θ : I.E)
    rw [sg_coe, star_mul, star_star, mul_comm]
  obtain ⟨c, hc⟩ := fixed_int I _ hfixy
  have hyP : θ * sg I θ ∈ P.asIdeal := Ideal.mul_mem_right _ _ hθP
  have hcv : c ∈ x.1.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
    rw [x.2]
    show c ∈ P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))
    rw [Ideal.mem_comap, hc]; exact hyP
  rw [Ideal.mem_comap, hc] at hcv
  rcases x.1.isPrime.mem_or_mem hcv with h | h
  · exact hθx h
  · apply hθx
    have : θ ∈ (cj I x.1).asIdeal := by rw [mem_cj]; exact h
    rwa [hcxx] at this
end PI.ScRefExists.TH
