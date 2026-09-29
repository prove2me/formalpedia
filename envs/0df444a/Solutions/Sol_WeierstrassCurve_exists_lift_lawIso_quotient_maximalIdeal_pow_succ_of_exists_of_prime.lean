-- Prove2me | solution 1 for WeierstrassCurve.exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2ee0f6be-36dd-5fb7-8d6f-fa1d8900cde4

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime
import Theorems.Thm_FormalGroup_IsBaseChange_isComm
import Theorems.Thm_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast"
p2m_attr_erase "simp" "MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace L2Aux

theorem exists_law (S : Type) [CommRing S] (W : WeierstrassCurve S) (hW : IsUnit W.Δ) :
    ∃ G : FormalGroup S, G.toPowerSeries = W.formalGroupLawFixed := by
  classical
  let P := MvPolynomial (Fin 5) ℤ
  let Wu : WeierstrassCurve P :=
    ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩
  have hΔ0 : Wu.Δ ≠ 0 := by
    intro h
    have h1 : (Wu.map (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ))).Δ = 0 := by
      rw [WeierstrassCurve.map_Δ, h, map_zero]
    have h2 : Wu.map (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ)) = ⟨0, 0, 0, -1, 0⟩ := by
      refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
      · show MvPolynomial.eval _ (MvPolynomial.X _) = _
        rw [MvPolynomial.eval_X]; rfl
    rw [h2] at h1
    revert h1
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  obtain ⟨D, hD⟩ : ∃ D : P, Wu.Δ = D := ⟨_, rfl⟩
  have hpow : Submonoid.powers D ≤ nonZeroDivisors P := powers_le_nonZeroDivisors_of_noZeroDivisors (hD ▸ hΔ0)
  let A := Localization.Away D
  haveI : IsDomain A := IsLocalization.isDomain_localization hpow
  let WA : WeierstrassCurve A := Wu.map (algebraMap P A)
  have hΔA : IsUnit WA.Δ := by
    rw [WeierstrassCurve.map_Δ, hD]; exact IsLocalization.Away.algebraMap_isUnit D
  haveI : WA.IsElliptic := ⟨hΔA⟩
  let φ₀ : P →+* S := MvPolynomial.eval₂Hom (Int.castRingHom S) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hφ₀W : Wu.map φ₀ = W := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    · show MvPolynomial.eval₂Hom (Int.castRingHom S) _ (MvPolynomial.X _) = _
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hφ₀Δ : IsUnit (φ₀ D) := by rw [← hD, ← WeierstrassCurve.map_Δ, hφ₀W]; exact hW
  let φ : A →+* S := IsLocalization.Away.lift D hφ₀Δ
  have hWφ : WA.map φ = W := by rw [WeierstrassCurve.map_map, IsLocalization.Away.lift_comp, hφ₀W]
  refine ⟨WA.formalGroup.map φ, ?_⟩
  rw [FormalGroup.map_toPowerSeries, ← hWφ, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map WA φ).2]; rfl

end L2Aux

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT E₀.formalGroup)
    (n : ℕ) (hn : 1 ≤ n)
    (h : ∃ (E : WeierstrassCurve T) (_ : E.map resT = E₀)
      (Gn : FormalGroup (T ⧸ maximalIdeal T ^ n))
      (_ : Gn.toPowerSeries = (E.map (Ideal.Quotient.mk (maximalIdeal T ^ n))).formalGroupLawFixed)
      (ψ : FormalGroup.LawIso Gn (G.map (Ideal.Quotient.mk (maximalIdeal T ^ n)))),
      ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈
        (maximalIdeal T).map (Ideal.Quotient.mk (maximalIdeal T ^ n))) :
    ∃ (E : WeierstrassCurve T) (_ : E.map resT = E₀)
      (Gn : FormalGroup (T ⧸ maximalIdeal T ^ (n + 1)))
      (_ : Gn.toPowerSeries = (E.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1)))).formalGroupLawFixed)
      (ψ : FormalGroup.LawIso Gn (G.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))))),
      ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈
        (maximalIdeal T).map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) := by
  classical
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hkerT, RingHom.mem_ker]

  set 𝔪 : Ideal T := maximalIdeal T with h𝔪
  set π' : T →+* T ⧸ 𝔪 ^ (n + 1) := Ideal.Quotient.mk (𝔪 ^ (n + 1)) with hπ'
  set πn : T →+* T ⧸ 𝔪 ^ n := Ideal.Quotient.mk (𝔪 ^ n) with hπn
  obtain ⟨E, hE, Gn, hGn, ψ, hψ⟩ := h
  have hπ'surj : Function.Surjective π' := Ideal.Quotient.mk_surjective
  have hle : 𝔪 ^ (n + 1) ≤ 𝔪 ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
  have hle1 : 𝔪 ^ (n + 1) ≤ 𝔪 := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hlen : 𝔪 ^ n ≤ 𝔪 := Ideal.pow_le_self (by omega)
  haveI : Nontrivial (T ⧸ 𝔪 ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun h => (maximalIdeal.isMaximal T).ne_top (top_le_iff.mp (h ▸ hle1)))
  haveI : IsLocalRing (T ⧸ 𝔪 ^ (n + 1)) := IsLocalRing.of_surjective' π' hπ'surj

  let res' : T ⧸ 𝔪 ^ (n + 1) →+* k := Ideal.Quotient.lift (𝔪 ^ (n + 1)) resT (fun a ha => (hmem a).mp (hle1 ha))
  have hres'π : ∀ x : T, res' (π' x) = resT x := fun x => Ideal.Quotient.lift_mk _ _ _
  have hres'surj : Function.Surjective res' := fun a => by
    obtain ⟨x, hx⟩ := hresT a; exact ⟨π' x, by rw [hres'π, hx]⟩
  have hker' : RingHom.ker res' = maximalIdeal (T ⧸ 𝔪 ^ (n + 1)) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective res' hres'surj)
  have hmax' : maximalIdeal (T ⧸ 𝔪 ^ (n + 1)) = 𝔪.map π' := by
    rw [← hker']
    ext x
    obtain ⟨y, rfl⟩ := hπ'surj x
    rw [RingHom.mem_ker, hres'π, ← hmem, Ideal.mem_map_iff_of_surjective π' hπ'surj]
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : y - z ∈ 𝔪 ^ (n + 1) := by rw [← Ideal.Quotient.eq, ← hπ']; exact hzy.symm
      have := 𝔪.add_mem (hle1 this) hz
      rwa [sub_add_cancel] at this

  set I : Ideal (T ⧸ 𝔪 ^ (n + 1)) := (𝔪 ^ n).map π' with hI
  have hIsmall : I * maximalIdeal (T ⧸ 𝔪 ^ (n + 1)) = ⊥ := by
    rw [hmax', hI, ← Ideal.map_mul, ← pow_succ, hπ', Ideal.map_quotient_self]
  have hIm : I ≤ maximalIdeal (T ⧸ 𝔪 ^ (n + 1)) := by rw [hmax', hI]; exact Ideal.map_mono hlen

  set G' : FormalGroup (T ⧸ 𝔪 ^ (n + 1)) := G.map π' with hG'def
  have hG'bc0 : G.IsBaseChange π' G' := by
    show G'.toPowerSeries = MvPowerSeries.map π' G.toPowerSeries; rw [hG'def, FormalGroup.map_toPowerSeries]
  haveI : G'.IsComm := FormalGroup.IsBaseChange.isComm G π' G' hG'bc0
  have hres'comp : res'.comp π' = resT := RingHom.ext hres'π
  have hG'bc : G'.IsBaseChange res' E₀.formalGroup := by
    show E₀.formalGroup.toPowerSeries = MvPowerSeries.map res' G'.toPowerSeries
    rw [hG'def, FormalGroup.map_toPowerSeries, MvPowerSeries.map_map, hres'comp]; exact hG
  set E₁ : WeierstrassCurve (T ⧸ 𝔪 ^ (n + 1)) := E.map π' with hE₁
  have hE₁res : E₁.map res' = E₀ := by rw [hE₁, WeierstrassCurve.map_map, hres'comp, hE]
  have hE₁Δ : IsUnit E₁.Δ := by
    by_contra hu
    have hm : E₁.Δ ∈ maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [← hker', RingHom.mem_ker, ← WeierstrassCurve.map_Δ, hE₁res] at hm
    exact E₀.isUnit_Δ.ne_zero hm
  obtain ⟨G₁, hG₁⟩ := L2Aux.exists_law _ E₁ hE₁Δ
  haveI : G₁.IsComm := ⟨by rw [hG₁]; exact WeierstrassCurve.formalGroupLawFixed_comm_of_commRing E₁⟩

  let e : (T ⧸ 𝔪 ^ (n + 1)) ⧸ I ≃+* T ⧸ 𝔪 ^ n := DoubleQuot.quotQuotEquivQuotOfLE hle
  let ε : T ⧸ 𝔪 ^ n →+* (T ⧸ 𝔪 ^ (n + 1)) ⧸ I := e.symm.toRingHom
  set mkI : T ⧸ 𝔪 ^ (n + 1) →+* (T ⧸ 𝔪 ^ (n + 1)) ⧸ I := Ideal.Quotient.mk I with hmkI
  have hεπ : ∀ x : T, ε (πn x) = mkI (π' x) := fun x => DoubleQuot.quotQuotEquivQuotOfLE_symm_mk x hle
  have hcomp : mkI.comp π' = ε.comp πn := RingHom.ext fun x => (hεπ x).symm
  set Gbar : FormalGroup ((T ⧸ 𝔪 ^ (n + 1)) ⧸ I) := (G.map πn).map ε with hGbar
  set G₁bar : FormalGroup ((T ⧸ 𝔪 ^ (n + 1)) ⧸ I) := Gn.map ε with hG₁bar
  have hGbar_bc : G'.IsBaseChange mkI Gbar := by
    show Gbar.toPowerSeries = MvPowerSeries.map mkI G'.toPowerSeries
    rw [hGbar, FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, hG'def, FormalGroup.map_toPowerSeries,
      MvPowerSeries.map_map, MvPowerSeries.map_map, hcomp]
  have hG₁bar_bc : G₁.IsBaseChange mkI G₁bar := by
    show G₁bar.toPowerSeries = MvPowerSeries.map mkI G₁.toPowerSeries
    rw [hG₁bar, FormalGroup.map_toPowerSeries, hGn, hG₁, hE₁,
      ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map _ ε).2,
      ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map _ mkI).2, WeierstrassCurve.map_map,
      WeierstrassCurve.map_map, hcomp]
  have hbc1 : Gn.IsBaseChange ε G₁bar := by
    show G₁bar.toPowerSeries = MvPowerSeries.map ε Gn.toPowerSeries; rw [hG₁bar, FormalGroup.map_toPowerSeries]
  have hbc2 : (G.map πn).IsBaseChange ε Gbar := by
    show Gbar.toPowerSeries = MvPowerSeries.map ε (G.map πn).toPowerSeries; rw [hGbar, FormalGroup.map_toPowerSeries]
  obtain ⟨θ, hθ⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map ε ψ.toLawHom G₁bar Gbar hbc1 hbc2
  have hθ1 : IsUnit (PowerSeries.coeff 1 θ.series) := by rw [hθ, PowerSeries.coeff_map]; exact ψ.isUnit_coeff_one.map _
  have hθm : ∀ m : ℕ, PowerSeries.coeff m θ.series - (if m = 1 then 1 else 0) ∈
      (maximalIdeal (T ⧸ 𝔪 ^ (n + 1))).map mkI := by
    intro m
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective πn Ideal.Quotient.mk_surjective).mp (hψ m)
    rw [hθ, PowerSeries.coeff_map, show ψ.toLawHom.series = ψ.series from rfl]
    have : PowerSeries.coeff m ψ.series = (if m = 1 then 1 else 0) + πn y := by rw [hyx]; ring
    rw [this, map_add]
    have : ε (if m = 1 then 1 else 0) = (if m = 1 then 1 else 0 : (T ⧸ 𝔪 ^ (n + 1)) ⧸ I) := by split_ifs <;> simp
    rw [this, add_sub_cancel_left, hεπ, hmax']
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hy)

  obtain ⟨E'', hE'', G'', hG'', ψ'', hψ''⟩ :=
    WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime q k E₀ hE₀
      (T ⧸ 𝔪 ^ (n + 1)) I hIsmall hIm res' hres'surj hker' G' hG'bc E₁ hE₁res G₁ hG₁ Gbar G₁bar hGbar_bc hG₁bar_bc ⟨θ, hθ1⟩ hθm

  choose b₁ hb₁ using hπ'surj E''.a₁
  choose b₂ hb₂ using hπ'surj E''.a₂
  choose b₃ hb₃ using hπ'surj E''.a₃
  choose b₄ hb₄ using hπ'surj E''.a₄
  choose b₆ hb₆ using hπ'surj E''.a₆
  let Et : WeierstrassCurve T := ⟨b₁, b₂, b₃, b₄, b₆⟩
  have hEt : Et.map π' = E'' := WeierstrassCurve.ext hb₁ hb₂ hb₃ hb₄ hb₆
  have hE''res : E''.map res' = E₀ := by
    rw [← hE₁res]
    obtain ⟨d1, d2, d3, d4, d6⟩ := WeierstrassCurve.ext_iff.mp hE''
    have key : ∀ x y : T ⧸ 𝔪 ^ (n + 1), mkI x = mkI y → res' x = res' y := by
      intro x y hxy
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker']
      exact hIm ((Ideal.Quotient.eq).mp (by rw [← hmkI]; exact hxy))
    exact WeierstrassCurve.ext (key _ _ d1) (key _ _ d2) (key _ _ d3) (key _ _ d4) (key _ _ d6)
  refine ⟨Et, ?_, G'', ?_, ψ'', fun m => ?_⟩
  · rw [← hres'comp, ← WeierstrassCurve.map_map, hEt, hE''res]
  · rw [hG'', ← hEt]
  · have h0 : res' (PowerSeries.coeff m ψ''.series - (if m = 1 then 1 else 0)) = 0 := by
      rw [map_sub, hψ'' m]; split_ifs <;> simp
    rw [← RingHom.mem_ker, hker', hmax'] at h0
    exact h0

end S_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime
end P2MW
export P2MW.S_WeierstrassCurve_exists_lift_lawIso_quotient_maximalIdeal_pow_succ_of_exists_of_prime (solution)
