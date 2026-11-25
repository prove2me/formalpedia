-- Prove2me | solution 1 for UnipMove.top_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:33.967287+00:00
-- url     : https://prove2.me/submissions/827373ea-5fff-46a0-b953-89f1df610ea0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_TopOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution (hemb : SEmb E) (hN1 : RadiusPosLeTenth) (hN2 : KatoClassHeckeEulerFactorRelation) (hN3 : UnipotentMoveNumericalInequalities) (hN4 : EpsilonZeroPos E)
    (hcmp : SCmp E) (hmf : SMajFlag E) (hflag : SFlagMap E) (hgraph : SGraph E)
    (hsplit : SSplit E) (hdelta : SDelta E)
    (hD4 : ShortVectorBound (E := E)) (hD2i : UnitaryComplementMove (E := E)) (hD2ii : ReducedFrameDomainCovering (E := E)) :
    UnitaryUnipotentMove (E := E) := by
  intro r X la P ξ ν c1 w z0 hH x0 hx0 hx0o hfl0 lam h1 Z1 hu1 hfix1 hpres1 hsp1 hfl1 hZ1 n' hn'
  have hD4' := hD4 r X la P ξ ν c1 w z0 hH
  obtain ⟨-, -, hiso, hc1, -, -, hw, -, -, hz0D1, -⟩ := hH
  obtain ⟨hρ0, hρ1⟩ := hN1 c1 w hc1 hw
  have hZ1' : X.zN Z1 < d6rh c1 w / 21 := by
    have : d6rh c1 w / 100 < d6rh c1 w / 21 := by linarith
    linarith
  rcases Nat.eq_zero_or_pos n' with rfl | hn'pos
  · have hone : X.lmulC (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (X.lmulC h1 z0) = X.lmulC h1 z0 := by
      funext τ; simp only [Data.lmulC, one_mul, mat, Matrix.of_apply]; rfl
    refine ⟨fun _ => 1, Z1, ?_, ?_, ?_, ?_, ?_, hZ1'⟩
    · intro τ u v; simp
    · intro τ; simp
    · intro μ _
      refine ⟨0, by simp, ?_⟩
      funext τ a; simp [Data.embV, Data.emb]
    · rw [hone]; exact hsp1
    · rw [hone]; exact hfl1

  have hz0dom : z0 ∈ X.dom := hz0D1.1
  obtain ⟨hz1dom, hap, hmajξ, -⟩ := hD2i r X.toData ξ hiso z0 hz0dom h1 hu1 hfix1 hpres1
  have hz1D1 : X.lmulC h1 z0 ∈ X.FramesOverBasis ξ := ⟨hz1dom, fun τ => by rw [hmajξ τ]; exact hz0D1.2 τ⟩
  have hρ'0 : 0 < d6rh c1 w / 100 := by positivity
  have hρ'1 : d6rh c1 w / 100 ≤ 1 / 10 := by linarith
  have hc := hcmp r X.toData x0 hx0 hx0o (d6rh c1 w / 100) hρ'0 hρ'1 Z1 hZ1 (X.lmulC h1 z0) hz1dom hfl1
  have hmz0 : X.maj z0 = X.maj x0 := hmf r X.toData z0 x0 hz0dom hx0 hfl0
  set ρ := d6rh c1 w with hρdef
  set t := (1 - ρ / 100) / (1 + ρ / 100) with htdef
  have ht0 : 0 < t := by rw [htdef]; apply div_pos <;> linarith
  have ht1 : t ≤ 1 := by rw [htdef, div_le_one (by linarith)]; linarith
  have htinv : (1 + ρ / 100) / (1 - ρ / 100) = 1 / t := by
    rw [htdef, one_div_div]
  set ep0 := flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w with hep0def
  have hep0 : 0 < ep0 := hN4 r X c1 w hc1 hw

  have hns : ∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, t * ep0 ≤ X.maj (X.lmulC h1 z0) τ (X.ucomp (X.lmulC h1 z0) ξ (X.embV x) τ) := by
    intro x hx hxξ hne
    obtain ⟨τ, hτ⟩ := hD4' x hx hxξ hne
    refine ⟨τ, ?_⟩
    have hI : X.embV x ∈ X.Iperp ξ := fun τ => by
      show hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0
      rw [hemb, hxξ, map_zero]
    have hu : X.ucomp (X.lmulC h1 z0) ξ (X.embV x) = X.ucomp z0 ξ (X.embV x) := by
      simp only [Data.ucomp, hap _ hI]
    rw [hu]
    have h1' := (hc τ (X.ucomp z0 ξ (X.embV x) τ)).1
    rw [hmz0] at hτ
    calc t * ep0 ≤ t * X.maj x0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
          mul_le_mul_of_nonneg_left hτ ht0.le
      _ ≤ _ := h1'
  obtain ⟨δ, hδb, hδΛ⟩ := hdelta r X ξ (X.lmulC h1 z0) (t * ep0) n' hiso (mul_pos ht0 hep0) hn'pos
    hz1D1 hns
  set ms := frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 with hmsdef
  set κ := frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC (t * ep0) / n' with hκdef
  have hrd : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  have hm := hN2 r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 t (abs_nonneg _) hrd (Nat.cast_nonneg _)
    hep0 ht0 ht1
  have hm' := (hN2 r (fdeg E) (dE E) (rdE E) X.NA X.NC (t * ep0) 1 (abs_nonneg _) hrd
    (Nat.cast_nonneg _) (mul_pos ht0 hep0) one_pos le_rfl).2
  have hn'R : (0 : ℝ) < n' := by exact_mod_cast hn'pos
  have hκ0 : 0 ≤ κ := div_nonneg hm' hn'R.le
  have hmsn : ms / n' ≤ ρ / 1000 := by
    rw [div_le_iff₀ hn'R]
    have h := hn'
    rw [div_le_iff₀ hρ0] at h
    linarith
  have hκρ : κ ≤ ρ / (1000 * t) := by
    calc κ ≤ ms / t / n' := div_le_div_of_nonneg_right hm.1 hn'R.le
      _ = ms / n' / t := by ring
      _ ≤ ρ / 1000 / t := div_le_div_of_nonneg_right hmsn ht0.le
      _ = ρ / (1000 * t) := by ring
  obtain ⟨hκ1, hη1, hfin⟩ := hN3 ρ κ hρ0 hρ1 hκ0 hκρ
  obtain ⟨n, hnu, hnξ, -, -, hnap, -, hnJ, hnb⟩ :=
    hD2ii r X.toData ξ hiso (X.lmulC h1 z0) hz1dom δ κ hκ0 hκ1 hδb

  have hnb0 : ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj x0 τ (Matrix.mulVec (n τ - 1) v) ≤ (3 * κ / t) ^ 2 * X.maj x0 τ v := by
    intro τ v
    have a1 := (hc τ (Matrix.mulVec (n τ - 1) v)).1
    have a2 := hnb τ v
    have a3 := (hc τ v).2
    rw [htinv] at a3
    have e1 : X.maj x0 τ (Matrix.mulVec (n τ - 1) v) ≤
        X.maj (X.lmulC h1 z0) τ (Matrix.mulVec (n τ - 1) v) / t := by
      rw [le_div_iff₀ ht0]; linarith
    have e2 : X.maj (X.lmulC h1 z0) τ v ≤ X.maj x0 τ v / t := by
      exact le_of_le_of_eq a3 (by ring)
    calc X.maj x0 τ (Matrix.mulVec (n τ - 1) v)
        ≤ X.maj (X.lmulC h1 z0) τ (Matrix.mulVec (n τ - 1) v) / t := e1
      _ ≤ (3 * κ) ^ 2 * X.maj (X.lmulC h1 z0) τ v / t := div_le_div_of_nonneg_right a2 ht0.le
      _ ≤ (3 * κ) ^ 2 * (X.maj x0 τ v / t) / t :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left e2 (sq_nonneg _)) ht0.le
      _ = (3 * κ / t) ^ 2 * X.maj x0 τ v := by field_simp
  have hη0 : 0 ≤ 3 * κ / t := by positivity
  obtain ⟨Z, hZfl, hZn⟩ := hgraph r X.toData x0 hx0 hx0o n Z1 (3 * κ / t) (ρ / 100) hη0
    (by positivity) hZ1 hη1 hnb0
  refine ⟨n, Z, hnu, hnξ, ?_, ?_, ?_, lt_of_le_of_lt hZn hfin⟩
  · intro μ hμ
    obtain ⟨e, he, hid⟩ := hδΛ μ hμ
    refine ⟨e, he, ?_⟩
    have hμξ : herm X.Gm μ ξ = 0 := (AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp hμ).2)
    have hI : X.embV μ ∈ X.Iperp ξ := fun τ => by
      show hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 ξ) = 0
      rw [hemb, hμξ, map_zero]
    rw [hnap _ hI]; exact hid
  · exact hsplit r X ξ _ (X.lmulC h1 z0) (X.lmulC n (X.lmulC h1 z0)) lam δ hiso hsp1
      (fun u hu => hnap u hu) (fun u hu => hnJ u hu)
  · exact fun τ => ((hflag r X.toData (X.lmulC h1 z0) (X.xZ x0 Z1) n hfl1) τ).trans (hZfl τ)
end UnipMove
