-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ce255de0-eb07-52d7-8744-f9d2e067c701

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Theorems.Thm_WeierstrassCurve_coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
import Theorems.Thm_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map
import Theorems.Thm_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot
import Theorems.Thm_FormalGroup_IsBaseChange_isComm
import Theorems.Thm_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Theorems.Thm_FormalGroup_LawIso_exists_symm_subst_eq_X
import Theorems.Thm_FormalGroup_LawHom_exists_comp_series_eq_subst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

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

namespace STAux

noncomputable def idHom {R : Type*} [CommRing R] (G : FormalGroup R) : FormalGroup.LawHom G G where
  series := PowerSeries.X
  constantCoeff_series := PowerSeries.constantCoeff_X
  comm := by
    have hF : PowerSeries.HasSubst G.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff
    have hsx : ∀ i : Fin 2, FormalGroup.LawHom.substX i (PowerSeries.X : PowerSeries R) = MvPowerSeries.X i := by
      intro i; unfold FormalGroup.LawHom.substX
      exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))
    have hvec : (![MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = MvPowerSeries.X := by
      funext i; fin_cases i <;> rfl
    rw [PowerSeries.subst_X hF, hsx, hsx, hvec, MvPowerSeries.subst_self, id]

@[scoped simp] theorem idHom_series {R : Type*} [CommRing R] (G : FormalGroup R) : (idHom G).series = PowerSeries.X := rfl

noncomputable def idIso {R : Type*} [CommRing R] (G : FormalGroup R) : FormalGroup.LawIso G G :=
  ⟨idHom G, by rw [idHom_series, PowerSeries.coeff_one_X]; exact isUnit_one⟩

end STAux
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso.STAux"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E E' : WeierstrassCurve T) (hE : E.map resT = E₀) (hE' : E'.map resT = E₀)
    (G : FormalGroup T) [G.IsComm] (hG : G.toPowerSeries = E.formalGroupLawFixed)
    (G' : FormalGroup T) [G'.IsComm] (hG' : G'.toPowerSeries = E'.formalGroupLawFixed)
    (ψ : FormalGroup.LawIso G G')
    (hψ : ∀ m : ℕ, resT (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0)
    (n : ℕ) (hn : 1 ≤ n)
    (C : WeierstrassCurve.VariableChange T) (hC : C.map resT = 1)
    (hCE : (C • E).map (Ideal.Quotient.mk (maximalIdeal T ^ n)) = E'.map (Ideal.Quotient.mk (maximalIdeal T ^ n))) :
    ∃ C' : WeierstrassCurve.VariableChange T, C'.map resT = 1 ∧
      (C' • E).map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) =
        E'.map (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))) := by
  classical
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hkerT, RingHom.mem_ker]
  have hprime : q.Prime := Fact.out

  have hEΔ : IsUnit E.Δ := by
    by_contra hu
    have hm : E.Δ ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [hmem, ← WeierstrassCurve.map_Δ, hE] at hm
    exact E₀.isUnit_Δ.ne_zero hm
  have hCE_res : (C • E).map resT = E₀ := by rw [← WeierstrassCurve.map_variableChange, hC, hE, one_smul]
  have hCEΔ : IsUnit (C • E).Δ := by
    rw [WeierstrassCurve.variableChange_Δ]; exact IsUnit.mul (IsUnit.pow _ (Units.isUnit _)) hEΔ
  obtain ⟨GC, hGC⟩ := L2Aux.exists_law T (C • E) hCEΔ
  haveI : GC.IsComm := ⟨by rw [hGC]; exact WeierstrassCurve.formalGroupLawFixed_comm_of_commRing _⟩
  set s : PowerSeries T := E.variableChangeSeries C with hs
  obtain ⟨hs1, hscomm⟩ := WeierstrassCurve.coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed E C
  let χ : FormalGroup.LawIso G GC :=
    { series := s
      constantCoeff_series := by rw [hs]; exact WeierstrassCurve.constantCoeff_variableChangeSeries E C
      comm := by
        rw [hG, hGC]
        show PowerSeries.subst E.formalGroupLawFixed s =
          MvPowerSeries.subst ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) T) s,
            PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) T) s] (C • E).formalGroupLawFixed
        rw [hs]; exact hscomm
      isUnit_coeff_one := by show IsUnit (PowerSeries.coeff 1 s); rw [hs, hs1]; exact Units.isUnit _ }
  have hχs : χ.series = s := rfl
  obtain ⟨χ', hχ1, hχ2⟩ := FormalGroup.LawIso.exists_symm_subst_eq_X χ
  obtain ⟨ω, hωs, hω1⟩ := FormalGroup.LawHom.exists_comp_series_eq_subst χ'.toLawHom ψ.toLawHom
  have hωu : IsUnit (PowerSeries.coeff 1 ω.series) := by
    rw [hω1]; exact IsUnit.mul ψ.isUnit_coeff_one χ'.isUnit_coeff_one

  have em : ∀ (S' : Type) [CommRing S'] (f : T →+* S') (p : PowerSeries T), MvPowerSeries.map f p = PowerSeries.map f p :=
    fun _ _ _ _ => rfl
  have hvc1 : ∀ (W : WeierstrassCurve k), W.variableChangeSeries 1 = PowerSeries.X := by
    intro W
    have hden : W.variableChangeDenom 1 = 1 := by
      unfold WeierstrassCurve.variableChangeDenom
      rw [WeierstrassCurve.VariableChange.one_def]; simp
    unfold WeierstrassCurve.variableChangeSeries
    rw [hden]
    have hinv : PowerSeries.invOfUnit (1 : PowerSeries k) 1 = 1 := by
      have := PowerSeries.mul_invOfUnit (1 : PowerSeries k) 1 (by simp)
      rwa [one_mul] at this
    rw [hinv, WeierstrassCurve.VariableChange.one_def]; simp
  have hsres : PowerSeries.map resT s = PowerSeries.X := by
    rw [hs, ← (WeierstrassCurve.variableChangeDenom_map_and_variableChangeSeries_map E C resT).2, hE, hC, hvc1]
  have hss : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero' χ.constantCoeff_series
  have hχ's : PowerSeries.HasSubst χ'.series := PowerSeries.HasSubst.of_constantCoeff_zero' χ'.constantCoeff_series
  have hχ'res : PowerSeries.map resT χ'.series = PowerSeries.X := by
    have := congrArg (PowerSeries.map resT) hχ1
    rw [hχs, PowerSeries.map_X, ← em, PowerSeries.map_subst hss] at this
    try simp only [em] at this
    rwa [hsres, PowerSeries.X_subst] at this
  have hωres : PowerSeries.map resT ω.series = PowerSeries.X := by
    rw [hωs, show χ'.toLawHom.series = χ'.series from rfl, show ψ.toLawHom.series = ψ.series from rfl, ← em,
      PowerSeries.map_subst hχ's]
    try simp only [em]
    have hψres : PowerSeries.map resT ψ.series = PowerSeries.X := by
      ext m; rw [PowerSeries.coeff_map, hψ m, PowerSeries.coeff_X]
    rw [hχ'res, hψres, PowerSeries.X_subst]

  set 𝔪 : Ideal T := maximalIdeal T with h𝔪
  set π' : T →+* T ⧸ 𝔪 ^ (n + 1) := Ideal.Quotient.mk (𝔪 ^ (n + 1)) with hπ'
  set πn : T →+* T ⧸ 𝔪 ^ n := Ideal.Quotient.mk (𝔪 ^ n) with hπn
  have hπ'surj : Function.Surjective π' := Ideal.Quotient.mk_surjective
  have hπnsurj : Function.Surjective πn := Ideal.Quotient.mk_surjective
  have hle : 𝔪 ^ (n + 1) ≤ 𝔪 ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
  have hle1 : 𝔪 ^ (n + 1) ≤ 𝔪 := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hlen : 𝔪 ^ n ≤ 𝔪 := Ideal.pow_le_self (by omega)
  haveI : Nontrivial (T ⧸ 𝔪 ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun h => (maximalIdeal.isMaximal T).ne_top (top_le_iff.mp (h ▸ hle1)))
  haveI : IsLocalRing (T ⧸ 𝔪 ^ (n + 1)) := IsLocalRing.of_surjective' π' hπ'surj
  let res' : T ⧸ 𝔪 ^ (n + 1) →+* k := Ideal.Quotient.lift (𝔪 ^ (n + 1)) resT (fun a ha => (hmem a).mp (hle1 ha))
  have hres'π : ∀ x : T, res' (π' x) = resT x := fun x => Ideal.Quotient.lift_mk _ _ _
  have hres'comp : res'.comp π' = resT := RingHom.ext hres'π
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

  let resn : T ⧸ 𝔪 ^ n →+* k := Ideal.Quotient.lift (𝔪 ^ n) resT (fun a ha => (hmem a).mp (hlen ha))
  have hresnπ : ∀ x : T, resn (πn x) = resT x := fun x => Ideal.Quotient.lift_mk _ _ _
  have hresncomp : resn.comp πn = resT := RingHom.ext hresnπ
  have hresnsurj : Function.Surjective resn := fun a => by
    obtain ⟨x, hx⟩ := hresT a; exact ⟨πn x, by rw [hresnπ, hx]⟩
  have hkern : RingHom.ker resn = 𝔪.map πn := by
    ext x
    obtain ⟨y, rfl⟩ := hπnsurj x
    rw [RingHom.mem_ker, hresnπ, ← hmem, Ideal.mem_map_iff_of_surjective πn hπnsurj]
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : y - z ∈ 𝔪 ^ n := by rw [← Ideal.Quotient.eq, ← hπn]; exact hzy.symm
      have := 𝔪.add_mem (hlen this) hz
      rwa [sub_add_cancel] at this
  have hkern_pow : RingHom.ker resn ^ n = ⊥ := by
    rw [hkern, ← Ideal.map_pow, hπn, Ideal.map_quotient_self]
  have hqn : (q : T ⧸ 𝔪 ^ n) ^ n = 0 := by
    have hq𝔪 : (q : T) ∈ 𝔪 := by rw [hmem, map_natCast, CharP.cast_eq_zero]
    have : ((q : T) ^ n) ∈ 𝔪 ^ n := Ideal.pow_mem_pow hq𝔪 n
    rw [← map_natCast πn, ← map_pow, hπn, Ideal.Quotient.eq_zero_iff_mem]; exact this

  set H : FormalGroup (T ⧸ 𝔪 ^ n) := G'.map πn with hH
  have hHbc' : G'.IsBaseChange πn H := by
    show H.toPowerSeries = MvPowerSeries.map πn G'.toPowerSeries; rw [hH, FormalGroup.map_toPowerSeries]
  have hHbcC : GC.IsBaseChange πn H := by
    show H.toPowerSeries = MvPowerSeries.map πn GC.toPowerSeries
    rw [hH, FormalGroup.map_toPowerSeries, hG', hGC, ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map _ πn).2,
      ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map _ πn).2, hπn, hCE]
  haveI : H.IsComm := FormalGroup.IsBaseChange.isComm G' πn H hHbc'
  have hHres : H.IsBaseChange resn E₀.formalGroup := by
    show E₀.formalGroup.toPowerSeries = MvPowerSeries.map resn H.toPowerSeries
    rw [hH, FormalGroup.map_toPowerSeries, MvPowerSeries.map_map, hresncomp, hG',
      ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E' resT).2, hE']; rfl
  obtain ⟨ωn, hωn⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map πn ω H H hHbcC hHbc'
  have hrig := FormalGroup.LawHom.series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot q resn hresnsurj n
    hkern_pow hqn E₀.formalGroup hE₀ H H hHres hHres ωn (STAux.idHom H) (by
      rw [hωn, STAux.idHom_series, PowerSeries.map_X]
      show MvPowerSeries.map resn (MvPowerSeries.map πn ω.series) = PowerSeries.X
      rw [MvPowerSeries.map_map, hresncomp]; exact hωres)

  have hωmod : ∀ m : ℕ, PowerSeries.coeff m ω.series - (if m = 1 then 1 else 0) ∈ 𝔪 ^ n := by
    intro m
    have e := congrArg (PowerSeries.coeff m) hωn
    rw [hrig, STAux.idHom_series, PowerSeries.coeff_X, PowerSeries.coeff_map] at e
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hπn, map_sub, ← e]
    split_ifs <;> simp

  set EC' : WeierstrassCurve (T ⧸ 𝔪 ^ (n + 1)) := (C • E).map π' with hEC'
  set E'' : WeierstrassCurve (T ⧸ 𝔪 ^ (n + 1)) := E'.map π' with hE''
  set GC' : FormalGroup (T ⧸ 𝔪 ^ (n + 1)) := GC.map π' with hGC'
  set G'' : FormalGroup (T ⧸ 𝔪 ^ (n + 1)) := G'.map π' with hG''
  have hEC'res : EC'.map res' = E₀ := by rw [hEC', WeierstrassCurve.map_map, hres'comp, hCE_res]

  let e : (T ⧸ 𝔪 ^ (n + 1)) ⧸ I ≃+* T ⧸ 𝔪 ^ n := DoubleQuot.quotQuotEquivQuotOfLE hle
  let ε : T ⧸ 𝔪 ^ n →+* (T ⧸ 𝔪 ^ (n + 1)) ⧸ I := e.symm.toRingHom
  set mkI : T ⧸ 𝔪 ^ (n + 1) →+* (T ⧸ 𝔪 ^ (n + 1)) ⧸ I := Ideal.Quotient.mk I with hmkI
  have hεπ : ∀ x : T, ε (πn x) = mkI (π' x) := fun x => DoubleQuot.quotQuotEquivQuotOfLE_symm_mk x hle
  have hcomp : mkI.comp π' = ε.comp πn := RingHom.ext fun x => (hεπ x).symm
  have hEE' : E''.map mkI = EC'.map mkI := by
    rw [hE'', hEC', WeierstrassCurve.map_map, WeierstrassCurve.map_map, hcomp, ← WeierstrassCurve.map_map,
      ← WeierstrassCurve.map_map, hπn, hCE]
  have hGC'ser : GC'.toPowerSeries = EC'.formalGroupLawFixed := by
    rw [hGC', FormalGroup.map_toPowerSeries, hGC, hEC', (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map _ π').2]
  have hG''ser : G''.toPowerSeries = E''.formalGroupLawFixed := by
    rw [hG'', FormalGroup.map_toPowerSeries, hG', hE'', (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map _ π').2]
  have hbcC : GC.IsBaseChange π' GC' := by
    show GC'.toPowerSeries = MvPowerSeries.map π' GC.toPowerSeries; rw [hGC', FormalGroup.map_toPowerSeries]
  have hbc' : G'.IsBaseChange π' G'' := by
    show G''.toPowerSeries = MvPowerSeries.map π' G'.toPowerSeries; rw [hG'', FormalGroup.map_toPowerSeries]
  obtain ⟨ω', hω'⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map π' ω GC' G'' hbcC hbc'
  have hω'1 : IsUnit (PowerSeries.coeff 1 ω'.series) := by rw [hω', PowerSeries.coeff_map]; exact hωu.map _
  have hω'I : ∀ m : ℕ, PowerSeries.coeff m ω'.series - (if m = 1 then 1 else 0) ∈ I := by
    intro m
    rw [hω', PowerSeries.coeff_map]
    have : π' (PowerSeries.coeff m ω.series - (if m = 1 then 1 else 0)) ∈ I := by
      rw [hI]; exact Ideal.mem_map_of_mem _ (hωmod m)
    rw [map_sub] at this
    convert this using 2
    split_ifs <;> simp
  obtain ⟨Cb, hCb1, hCbE⟩ :=
    WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot q hq k E₀ hE₀
      (T ⧸ 𝔪 ^ (n + 1)) I hIsmall hIm res' hres'surj hker' EC' E'' hEC'res hEE' GC' hGC'ser G'' hG''ser ⟨ω', hω'1⟩ hω'I

  choose cu hcu using hπ'surj ((Cb.u : (T ⧸ 𝔪 ^ (n + 1))ˣ) : T ⧸ 𝔪 ^ (n + 1))
  choose cr hcr using hπ'surj Cb.r
  choose cs hcs using hπ'surj Cb.s
  choose ct hct using hπ'surj Cb.t

  let resI : (T ⧸ 𝔪 ^ (n + 1)) ⧸ I →+* k := Ideal.Quotient.lift I res' (fun a ha => by
    rw [← RingHom.mem_ker, hker']; exact hIm ha)
  have hresI : ∀ x, resI (mkI x) = res' x := fun x => Ideal.Quotient.lift_mk _ _ _
  have hresIcomp : resI.comp mkI = res' := RingHom.ext hresI
  have hCbres : Cb.map res' = 1 := by
    rw [← hresIcomp, ← WeierstrassCurve.VariableChange.map_map, hCb1]
    exact map_one (WeierstrassCurve.VariableChange.mapHom resI)
  have hcu_unit : IsUnit cu := by
    by_contra hu
    have : cu ∈ 𝔪 := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [hmem, ← hres'π, hcu] at this
    have e1 := congrArg (fun D : WeierstrassCurve.VariableChange k => ((D.u : kˣ) : k)) hCbres
    simp only [WeierstrassCurve.VariableChange.map] at e1
    rw [Units.coe_map, MonoidHom.coe_coe] at e1
    rw [e1] at this
    exact one_ne_zero this
  obtain ⟨cuu, hcuu⟩ := hcu_unit
  let Cl : WeierstrassCurve.VariableChange T := ⟨cuu, cr, cs, ct⟩
  have hClπ : Cl.map π' = Cb := by
    apply WeierstrassCurve.VariableChange.ext
    · apply Units.ext
      show π' ((cuu : Tˣ) : T) = _; rw [hcuu, hcu]
    · exact hcr
    · exact hcs
    · exact hct
  have hClres : Cl.map resT = 1 := by
    rw [← hres'comp, ← WeierstrassCurve.VariableChange.map_map, hClπ, hCbres]
  refine ⟨Cl * C, ?_, ?_⟩
  · rw [show (Cl * C).map resT = Cl.map resT * C.map resT from map_mul (WeierstrassCurve.VariableChange.mapHom resT) Cl C,
      hClres, hC, one_mul]
  · rw [mul_smul, ← WeierstrassCurve.map_variableChange, hClπ, ← hEC', hCbE]

end S_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_map_eq_one_and_map_smul_eq_map_pow_succ_of_lawIso (solution)
