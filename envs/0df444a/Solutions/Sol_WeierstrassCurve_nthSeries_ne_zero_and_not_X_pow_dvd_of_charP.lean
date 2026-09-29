-- Prove2me | solution 1 for WeierstrassCurve.nthSeries_ne_zero_and_not_X_pow_dvd_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2457ca5d-9c78-5e7b-b103-8049c93fe898

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_prePsi_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_exists_genericPoint_formalGroupLawFixed_eq_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_nthSeries_ne_zero_and_not_X_pow_dvd_of_charP
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
set_option autoImplicit false
open FormalGroup
namespace OBAux
open MvPowerSeries
section Bridge
variable {R : Type*} [CommRing R]

theorem subst_elim_ofFormalGroup (F : FormalGroup R) {τ : Type*} {a b : MvPowerSeries τ R}
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) (i : Fin 1) :
    subst (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)) ((MvFormalGroup.ofFormalGroup F).toPowerSeries i)
      = subst ![a, b] F.toPowerSeries := by
  have hfam : HasSubst (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact ha
    · exact hb
  show subst (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)) (rename MvFormalGroup.e2 F.toPowerSeries) = _
  rw [MvFormalGroup.subst_rename MvFormalGroup.e2 hfam, MvFormalGroup.sumElim_comp_e2]

theorem subst_pair_assoc (F : FormalGroup R) {τ : Type*} {a b c : MvPowerSeries τ R}
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) (hc : c.constantCoeff = 0) :
    subst ![subst ![a, b] F.toPowerSeries, c] F.toPowerSeries
      = subst ![a, subst ![b, c] F.toPowerSeries] F.toPowerSeries := by
  have h := MvFormalGroup.subst_elim_assoc (MvFormalGroup.ofFormalGroup F)
    (a := fun _ : Fin 1 => a) (b := fun _ : Fin 1 => b) (c := fun _ : Fin 1 => c)
    (fun _ => ha) (fun _ => hb) (fun _ => hc) 0
  have hab : (fun j : Fin 1 => subst (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => b))
      ((MvFormalGroup.ofFormalGroup F).toPowerSeries j)) = fun _ : Fin 1 => subst ![a, b] F.toPowerSeries :=
    funext fun j => subst_elim_ofFormalGroup F ha hb j
  have hbc : (fun j : Fin 1 => subst (Sum.elim (fun _ : Fin 1 => b) (fun _ : Fin 1 => c))
      ((MvFormalGroup.ofFormalGroup F).toPowerSeries j)) = fun _ : Fin 1 => subst ![b, c] F.toPowerSeries :=
    funext fun j => subst_elim_ofFormalGroup F hb hc j
  rw [hab, hbc] at h
  have cab : (subst ![a, b] F.toPowerSeries).constantCoeff = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨ha, hb⟩))
      (Fin.forall_fin_two.mpr ⟨ha, hb⟩) F.zero_constantCoeff
  have cbc : (subst ![b, c] F.toPowerSeries).constantCoeff = 0 :=
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hb, hc⟩))
      (Fin.forall_fin_two.mpr ⟨hb, hc⟩) F.zero_constantCoeff
  rwa [subst_elim_ofFormalGroup F cab hc, subst_elim_ofFormalGroup F ha cbc] at h

theorem subst_pair_zero_right (F : FormalGroup R) {τ : Type*} {a : MvPowerSeries τ R}
    (ha : a.constantCoeff = 0) : subst ![a, 0] F.toPowerSeries = a := by
  have h1 : subst ![(X 0 : MvPowerSeries (Fin 1) R), 0] F.toPowerSeries = X 0 := by
    have h0 := MvFormalGroup.subst_elim_X_zero (MvFormalGroup.ofFormalGroup F) 0
    have hfe : (Sum.elim (fun j : Fin 1 => (X j : MvPowerSeries (Fin 1) R)) (fun _ : Fin 1 => 0))
        = Sum.elim (fun _ : Fin 1 => (X 0 : MvPowerSeries (Fin 1) R)) (fun _ : Fin 1 => 0) := by
      funext s
      rcases s with j | j
      · simp only [Sum.elim_inl, Subsingleton.elim j (0 : Fin 1)]
      · rfl
    rw [hfe, subst_elim_ofFormalGroup F (constantCoeff_X 0)
      (by exact map_zero (constantCoeff : MvPowerSeries (Fin 1) R →+* R)) 0] at h0
    exact h0
  have hc : HasSubst (fun _ : Fin 1 => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  have hX0 : HasSubst ((![(X 0 : MvPowerSeries (Fin 1) R), 0] : Fin 2 → MvPowerSeries (Fin 1) R)) :=
    hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [constantCoeff_X])
  have hfam : (fun s : Fin 2 => subst (fun _ : Fin 1 => a)
      ((![(X 0 : MvPowerSeries (Fin 1) R), 0] : Fin 2 → MvPowerSeries (Fin 1) R) s))
      = (![a, 0] : Fin 2 → MvPowerSeries τ R) := by
    funext s
    fin_cases s
    · exact subst_X hc 0
    · show subst (fun _ : Fin 1 => a) (0 : MvPowerSeries (Fin 1) R) = (0 : MvPowerSeries τ R)
      rw [← coe_substAlgHom hc, map_zero]
  calc subst ![a, 0] F.toPowerSeries
      = subst (fun s : Fin 2 => subst (fun _ : Fin 1 => a)
          ((![(X 0 : MvPowerSeries (Fin 1) R), 0] : Fin 2 → MvPowerSeries (Fin 1) R) s)) F.toPowerSeries := by
        rw [hfam]
    _ = subst (fun _ : Fin 1 => a) (subst ![(X 0 : MvPowerSeries (Fin 1) R), 0] F.toPowerSeries) :=
        (subst_comp_subst_apply hX0 hc _).symm
    _ = subst (fun _ : Fin 1 => a) (X 0 : MvPowerSeries (Fin 1) R) := by rw [h1]
    _ = a := subst_X hc 0

theorem subst_pair_zero_left (F : FormalGroup R) {τ : Type*} {a : MvPowerSeries τ R}
    (ha : a.constantCoeff = 0) : subst ![0, a] F.toPowerSeries = a := by
  have h1 : subst ![(0 : MvPowerSeries (Fin 1) R), X 0] F.toPowerSeries = X 0 := by
    have h0 := MvFormalGroup.subst_elim_zero_X (MvFormalGroup.ofFormalGroup F) 0
    have hfe : (Sum.elim (fun _ : Fin 1 => 0) (fun j : Fin 1 => (X j : MvPowerSeries (Fin 1) R)))
        = Sum.elim (fun _ : Fin 1 => (0 : MvPowerSeries (Fin 1) R)) (fun _ : Fin 1 => X 0) := by
      funext s
      rcases s with j | j
      · rfl
      · simp only [Sum.elim_inr, Subsingleton.elim j (0 : Fin 1)]
    rw [hfe, subst_elim_ofFormalGroup F
      (by exact map_zero (constantCoeff : MvPowerSeries (Fin 1) R →+* R)) (constantCoeff_X 0) 0] at h0
    exact h0
  have hc : HasSubst (fun _ : Fin 1 => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  have hX0 : HasSubst ((![(0 : MvPowerSeries (Fin 1) R), X 0] : Fin 2 → MvPowerSeries (Fin 1) R)) :=
    hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [constantCoeff_X])
  have hfam : (fun s : Fin 2 => subst (fun _ : Fin 1 => a)
      ((![(0 : MvPowerSeries (Fin 1) R), X 0] : Fin 2 → MvPowerSeries (Fin 1) R) s))
      = (![0, a] : Fin 2 → MvPowerSeries τ R) := by
    funext s
    fin_cases s
    · show subst (fun _ : Fin 1 => a) (0 : MvPowerSeries (Fin 1) R) = (0 : MvPowerSeries τ R)
      rw [← coe_substAlgHom hc, map_zero]
    · exact subst_X hc 0
  calc subst ![0, a] F.toPowerSeries
      = subst (fun s : Fin 2 => subst (fun _ : Fin 1 => a)
          ((![(0 : MvPowerSeries (Fin 1) R), X 0] : Fin 2 → MvPowerSeries (Fin 1) R) s)) F.toPowerSeries := by
        rw [hfam]
    _ = subst (fun _ : Fin 1 => a) (subst ![(0 : MvPowerSeries (Fin 1) R), X 0] F.toPowerSeries) :=
        (subst_comp_subst_apply hX0 hc _).symm
    _ = subst (fun _ : Fin 1 => a) (X 0 : MvPowerSeries (Fin 1) R) := by rw [h1]
    _ = a := subst_X hc 0

theorem nthSeries_one (F : FormalGroup R) : F.nthSeries 1 = PowerSeries.X := by
  rw [FormalGroup.nthSeries_succ, FormalGroup.nthSeries_zero]
  exact subst_pair_zero_left F (by simp [PowerSeries.X])
end Bridge
end OBAux
namespace OBAux
open MvPowerSeries
noncomputable section Series
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

theorem constantCoeff_psubst {τ : Type*} {s : MvPowerSeries τ R} (hs : MvPowerSeries.constantCoeff s = 0)
    (f : PowerSeries R) :
    MvPowerSeries.constantCoeff (PowerSeries.subst s f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs),
    finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hs, zero_pow hd, smul_zero])]
  rw [pow_zero, map_one, smul_eq_mul, mul_one, PowerSeries.coeff_zero_eq_constantCoeff]

theorem order_fgGenW_eq (s : PowerSeries R) (hs : PowerSeries.constantCoeff s = 0) :
    PowerSeries.order (W.fgGenW s : PowerSeries R) = 3 * PowerSeries.order s := by
  have hs' : MvPowerSeries.constantCoeff (s : MvPowerSeries Unit R) = 0 := hs
  have ha : PowerSeries.HasSubst (s : MvPowerSeries Unit R) := PowerSeries.HasSubst.of_constantCoeff_zero hs'
  have h := congrArg (PowerSeries.subst (s : MvPowerSeries Unit R)) W.formalW_mul_wUnitFactor
  rw [PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha] at h
  have hu : IsUnit (PowerSeries.subst s W.wUnitFactor : PowerSeries R) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    have : PowerSeries.constantCoeff (PowerSeries.subst s W.wUnitFactor : PowerSeries R) = 1 := by
      show MvPowerSeries.constantCoeff _ = 1
      rw [constantCoeff_psubst hs', W.constantCoeff_wUnitFactor]
    rw [this]; exact isUnit_one
  have ho := congrArg PowerSeries.order h
  rw [PowerSeries.order_mul, PowerSeries.order_zero_of_unit hu, _root_.add_zero, PowerSeries.order_pow] at ho
  rw [show (W.fgGenW s : PowerSeries R) = PowerSeries.subst s W.formalW from rfl, ho]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]

abbrev emb (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f
omit W in
theorem hasSubst_X1 : PowerSeries.HasSubst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)
omit W in
theorem emb_X : emb (PowerSeries.X : PowerSeries R) = MvPowerSeries.X 1 :=
  PowerSeries.subst_X hasSubst_X1
omit W in
theorem constantCoeff_emb (f : PowerSeries R) :
    MvPowerSeries.constantCoeff (emb f) = PowerSeries.constantCoeff f :=
  constantCoeff_psubst (MvPowerSeries.constantCoeff_X 1) f
omit W in

theorem coeff_emb (f : PowerSeries R) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n) (emb f) = PowerSeries.coeff n f := by
  classical
  rw [show emb f = PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f from rfl,
    PowerSeries.coeff_subst hasSubst_X1]
  rw [finsum_eq_single _ n ?vanish]
  · rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  case vanish =>
    intro m hm
    rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
    exact fun he => hm (by
      have h2 := congrArg (fun f => f (1 : Fin 2)) he
      simp only [Finsupp.single_eq_same] at h2
      omega)
omit W in

theorem noVar_emb (f : PowerSeries R) : WeierstrassCurve.NoVar (0 : Fin 2) (emb f) := by
  intro d hd
  rw [show emb f = PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f from rfl,
    PowerSeries.coeff_subst hasSubst_X1]
  have hterm : ∀ n, (PowerSeries.coeff n f) • MvPowerSeries.coeff d
      ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ n) = 0 := by
    intro n
    rw [(WeierstrassCurve.kwB_noVar_pow (WeierstrassCurve.noVar_X (by decide)) n) d hd, smul_zero]
  rw [finsum_congr hterm, finsum_zero]
omit W in
theorem coeff_single_zero_emb (f : PowerSeries R) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (emb f) = 0 :=
  noVar_emb f _ (by simp)
omit W in
theorem emb_eq_zero_iff (f : PowerSeries R) : emb f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext n
    rw [← coeff_emb f n, h, map_zero, map_zero]
  · intro h
    rw [h, show emb (0 : PowerSeries R) = PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) 0
      from rfl, ← PowerSeries.coe_substAlgHom hasSubst_X1, map_zero]

theorem emb_fgGenW (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) :
    emb (W.fgGenW f) = W.fgGenW (emb f) := by
  show PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)
      (PowerSeries.subst (f : MvPowerSeries Unit R) W.formalW)
    = PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f) W.formalW
  exact PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero (show MvPowerSeries.constantCoeff (f : MvPowerSeries Unit R) = 0 from hf))
    hasSubst_X1 W.formalW
omit W in

theorem emb_subst_pair (a b : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0)
    (hb : PowerSeries.constantCoeff b = 0) (G : MvPowerSeries (Fin 2) R) :
    emb (MvPowerSeries.subst ![a, b] G) = MvPowerSeries.subst ![emb a, emb b] G := by
  have hab : MvPowerSeries.HasSubst (![a, b] : Fin 2 → PowerSeries R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
      fin_cases i
      · exact ha
      · exact hb)
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X 1)
  show MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R))
      (MvPowerSeries.subst ![a, b] G) = _
  rw [MvPowerSeries.subst_comp_subst_apply hab hX]
  congr 1
  funext s
  fin_cases s <;> rfl

abbrev rhoFam (m : ℕ) : Fin 2 → PowerSeries R := ![PowerSeries.X, PowerSeries.X ^ m]
omit W in
theorem hasSubst_rhoFam {m : ℕ} (hm : m ≠ 0) : MvPowerSeries.HasSubst (rhoFam (R := R) m) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    fin_cases i
    · exact MvPowerSeries.constantCoeff_X ()
    · show PowerSeries.constantCoeff (PowerSeries.X ^ m) = 0
      rw [map_pow, PowerSeries.constantCoeff_X, zero_pow hm])
omit W in
theorem rhoFam_constantCoeff {m : ℕ} (hm : m ≠ 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff (rhoFam (R := R) m i) = 0 := by
  fin_cases i
  · exact MvPowerSeries.constantCoeff_X ()
  · show PowerSeries.constantCoeff (PowerSeries.X ^ m) = 0
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow hm]

theorem rho_fgGenW {m : ℕ} (hm : m ≠ 0) {a : MvPowerSeries (Fin 2) R} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst (rhoFam (R := R) m) (W.fgGenW a) = W.fgGenW (MvPowerSeries.subst (rhoFam (R := R) m) a) :=
  WeierstrassCurve.subst_pair_bridge (hasSubst_rhoFam hm) (PowerSeries.HasSubst.of_constantCoeff_zero ha) W.formalW
omit W in

theorem rho_emb {m : ℕ} (hm : m ≠ 0) (f : PowerSeries R) :
    MvPowerSeries.subst (rhoFam (R := R) m) (emb f) = PowerSeries.subst (PowerSeries.X ^ m : PowerSeries R) f := by
  have h : MvPowerSeries.subst (rhoFam (R := R) m) (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) = (PowerSeries.X ^ m : PowerSeries R) :=
    MvPowerSeries.subst_X (hasSubst_rhoFam hm) 1
  rw [show emb f = PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) f from rfl]
  show MvPowerSeries.subst (rhoFam (R := R) m)
      (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)) f) = _
  rw [MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X 1)) (hasSubst_rhoFam hm)]
  show MvPowerSeries.subst (fun _ : Unit => MvPowerSeries.subst (rhoFam (R := R) m) (MvPowerSeries.X (1 : Fin 2))) f = _
  rw [h]
  rfl
omit W in

theorem coeff_one_rho {m : ℕ} (hm : 2 ≤ m) {a : MvPowerSeries (Fin 2) R}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (rhoFam (R := R) m) a : PowerSeries R)
      = MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) a := by
  classical
  have hm0 : m ≠ 0 := by omega
  have h := MvFormalGroup.coeff_single_subst (c := rhoFam (R := R) m) (rhoFam_constantCoeff hm0) a ()
  rw [Fin.sum_univ_two] at h
  have c0 : MvPowerSeries.coeff (Finsupp.single () 1) (rhoFam (R := R) m 0) = 1 := by
    show PowerSeries.coeff 1 (PowerSeries.X : PowerSeries R) = 1
    exact PowerSeries.coeff_one_X
  have c1 : MvPowerSeries.coeff (Finsupp.single () 1) (rhoFam (R := R) m 1) = 0 := by
    show PowerSeries.coeff 1 ((PowerSeries.X : PowerSeries R) ^ m) = 0
    rw [PowerSeries.coeff_X_pow, if_neg (by omega)]
  rw [c0, c1, mul_one, mul_zero, _root_.add_zero] at h
  exact h
omit W in
theorem constantCoeff_rho {m : ℕ} (hm : m ≠ 0) {a : MvPowerSeries (Fin 2) R}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (MvPowerSeries.subst (rhoFam (R := R) m) a : PowerSeries R) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_rhoFam hm) (rhoFam_constantCoeff hm) (by exact ha)
omit W in

theorem order_rho_eq_one {m : ℕ} (hm : 2 ≤ m) {a : MvPowerSeries (Fin 2) R}
    (ha : MvPowerSeries.constantCoeff a = 0) (h1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) a = 1) :
    PowerSeries.order (MvPowerSeries.subst (rhoFam (R := R) m) a : PowerSeries R) = 1 := by
  have hm0 : m ≠ 0 := by omega
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
  refine ⟨?_, ?_⟩
  · rw [coeff_one_rho hm ha, h1]; exact one_ne_zero
  · intro i hi
    have : i = 0 := by omega
    subst this
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_rho hm0 ha

theorem N_ne_zero {a : MvPowerSeries (Fin 2) R}
    (ha : MvPowerSeries.constantCoeff a = 0) (h1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) a = 1) :
    a * W.fgGenW (MvPowerSeries.X 1) - (MvPowerSeries.X 1) * W.fgGenW a ≠ 0 := by
  intro h
  have hρ := congrArg (MvPowerSeries.subst (rhoFam (R := R) 2)) h
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_rhoFam (by norm_num)), map_sub, map_mul, map_mul, map_zero,
    MvPowerSeries.coe_substAlgHom] at hρ
  rw [rho_fgGenW W (by norm_num) (MvPowerSeries.constantCoeff_X 1), rho_fgGenW W (by norm_num) ha,
    MvPowerSeries.subst_X (hasSubst_rhoFam (by norm_num)) 1] at hρ
  set r : PowerSeries R := MvPowerSeries.subst (rhoFam (R := R) 2) a with hr
  have hro : PowerSeries.order r = 1 := order_rho_eq_one (le_refl 2) ha h1
  have hrc : PowerSeries.constantCoeff r = 0 := constantCoeff_rho (by norm_num) ha
  have hX2 : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries R) ^ 2) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow two_ne_zero]
  have o1 : PowerSeries.order (r * W.fgGenW ((PowerSeries.X : PowerSeries R) ^ 2) : PowerSeries R) = 7 := by
    rw [PowerSeries.order_mul, order_fgGenW_eq W _ hX2, PowerSeries.order_X_pow, hro]; norm_num
  have o2 : PowerSeries.order ((PowerSeries.X : PowerSeries R) ^ 2 * W.fgGenW r : PowerSeries R) = 5 := by
    rw [PowerSeries.order_mul, order_fgGenW_eq W _ hrc, PowerSeries.order_X_pow, hro]; norm_num
  have hne : PowerSeries.order (r * W.fgGenW ((PowerSeries.X : PowerSeries R) ^ 2) : PowerSeries R)
      ≠ PowerSeries.order (-((PowerSeries.X : PowerSeries R) ^ 2 * W.fgGenW r) : PowerSeries R) := by
    rw [PowerSeries.order_neg, o1, o2]; decide
  have o3 := PowerSeries.order_add_of_order_ne _ _ hne
  rw [PowerSeries.order_neg, o1, o2, ← sub_eq_add_neg] at o3
  have hz : (r * W.fgGenW ((PowerSeries.X : PowerSeries R) ^ 2) - (PowerSeries.X : PowerSeries R) ^ 2 * W.fgGenW r
      : PowerSeries R) = 0 := hρ
  rw [hz, PowerSeries.order_zero] at o3
  exact absurd o3 (by decide)
end Series
end OBAux
namespace OBAux
open MvPowerSeries
noncomputable section Homog
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

def homog {τ : Type*} (p : Polynomial R) (d : ℕ) (a b : MvPowerSeries τ R) : MvPowerSeries τ R :=
  ∑ i ∈ Finset.range (d + 1), MvPowerSeries.C (p.coeff i) * a ^ i * b ^ (d - i)
omit W in

theorem eval_homog {τ : Type*} (p : Polynomial R) (d : ℕ) (hd : p.natDegree ≤ d) (a b : MvPowerSeries τ R)
    (hb : WeierstrassCurve.genι b ≠ 0) :
    WeierstrassCurve.genι b ^ d *
        (p.map (algebraMap R (WeierstrassCurve.GenK τ R))).eval (WeierstrassCurve.genι a / WeierstrassCurve.genι b)
      = WeierstrassCurve.genι (homog p d a b) := by
  have hCalg : ∀ r : R, algebraMap R (WeierstrassCurve.GenK τ R) r
      = WeierstrassCurve.genι (MvPowerSeries.C r : MvPowerSeries τ R) := fun r => by
    rw [IsScalarTower.algebraMap_apply R (MvPowerSeries τ R) (WeierstrassCurve.GenK τ R) r]; rfl
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range' (algebraMap R _) (show p.natDegree < d + 1 by omega),
    Finset.mul_sum, homog, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := by
    have := Finset.mem_range.mp hi; omega
  rw [map_mul, map_mul, map_pow, map_pow, hCalg, div_pow]
  have hbi : WeierstrassCurve.genι b ^ i ≠ 0 := pow_ne_zero i hb
  rw [show WeierstrassCurve.genι b ^ d = WeierstrassCurve.genι b ^ (d - i) * WeierstrassCurve.genι b ^ i by
    rw [← pow_add, Nat.sub_add_cancel hi']]
  field_simp

abbrev homog₁ (p : Polynomial R) (d : ℕ) : PowerSeries R :=
  homog p d (PowerSeries.X : PowerSeries R) (W.formalW : PowerSeries R)

theorem emb_homog₁ (p : Polynomial R) (d : ℕ) :
    emb (homog₁ W p d) = homog p d (MvPowerSeries.X (1 : Fin 2)) (W.fgGenW (MvPowerSeries.X 1)) := by
  simp only [homog₁, homog]
  rw [show emb (∑ i ∈ Finset.range (d + 1), MvPowerSeries.C (p.coeff i) * (PowerSeries.X : PowerSeries R) ^ i *
      (W.formalW : PowerSeries R) ^ (d - i))
    = PowerSeries.substAlgHom hasSubst_X1 (∑ i ∈ Finset.range (d + 1),
      MvPowerSeries.C (p.coeff i) * (PowerSeries.X : PowerSeries R) ^ i * (W.formalW : PowerSeries R) ^ (d - i))
    by rw [PowerSeries.coe_substAlgHom]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hasSubst_X1]
  have hC : PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)
      (MvPowerSeries.C (p.coeff i) : PowerSeries R) = MvPowerSeries.C (p.coeff i) := PowerSeries.subst_C _
  rw [hC]
  rfl

theorem formalW_pow (m : ℕ) : ∃ v : PowerSeries R, PowerSeries.constantCoeff v = 1 ∧
    (W.formalW : PowerSeries R) ^ m = (PowerSeries.X : PowerSeries R) ^ (3 * m) * v := by
  obtain ⟨u, hu1, hu⟩ := W.exists_eq_X_pow_three_mul
  refine ⟨u ^ m, by rw [map_pow, hu1, one_pow], ?_⟩
  rw [hu, mul_pow, ← pow_mul]

theorem order_homog₁ (p : Polynomial R) (d : ℕ) (hd : p.natDegree ≤ d) (hp : p ≠ 0) :
    PowerSeries.order (homog₁ W p d) = ((3 * d - 2 * p.natDegree : ℕ) : ℕ∞) := by
  classical
  set e := p.natDegree with he
  have key : ∀ i ∈ Finset.range (d + 1), ∃ g : PowerSeries R,
      MvPowerSeries.C (p.coeff i) * (PowerSeries.X : PowerSeries R) ^ i * (W.formalW : PowerSeries R) ^ (d - i)
        = (PowerSeries.X : PowerSeries R) ^ (3 * d - 2 * i) * g ∧ PowerSeries.constantCoeff g = p.coeff i := by
    intro i hi
    have hi' : i ≤ d := by have := Finset.mem_range.mp hi; omega
    obtain ⟨v, hv1, hv⟩ := formalW_pow W (d - i)
    refine ⟨PowerSeries.C (p.coeff i) * v, ?_, by rw [map_mul, PowerSeries.constantCoeff_C, hv1, mul_one]⟩
    rw [hv, show (MvPowerSeries.C (p.coeff i) : PowerSeries R) = PowerSeries.C (p.coeff i) from rfl]
    have : 3 * d - 2 * i = i + 3 * (d - i) := by omega
    rw [this, pow_add]; ring
  have hdiv : ∀ n < 3 * d - 2 * e, PowerSeries.coeff n (homog₁ W p d) = 0 := by
    intro n hn
    simp only [homog₁, homog, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨g, hg, -⟩ := key i hi
    by_cases hci : p.coeff i = 0
    · rw [hci, map_zero, zero_mul, zero_mul, map_zero]
    · have hie : i ≤ e := Polynomial.le_natDegree_of_ne_zero hci
      rw [hg, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hlead : PowerSeries.coeff (3 * d - 2 * e) (homog₁ W p d) = p.leadingCoeff := by
    simp only [homog₁, homog, map_sum]
    rw [Finset.sum_eq_single_of_mem e (Finset.mem_range.mpr (by omega))]
    · obtain ⟨g, hg, hgc⟩ := key e (Finset.mem_range.mpr (by omega))
      rw [hg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        hgc, Polynomial.leadingCoeff, he]
    · intro i hi hne
      obtain ⟨g, hg, -⟩ := key i hi
      by_cases hci : p.coeff i = 0
      · rw [hci, map_zero, zero_mul, zero_mul, map_zero]
      · have hie : i < e := lt_of_le_of_ne (Polynomial.le_natDegree_of_ne_zero hci) hne
        rw [hg, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [PowerSeries.order_eq_nat]
  exact ⟨by rw [hlead]; exact Polynomial.leadingCoeff_ne_zero.mpr hp, hdiv⟩
end Homog
noncomputable section Main
variable {k : Type} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]

def useq (F : FormalGroup k) (n : ℕ) : MvPowerSeries (Fin 2) k := emb (F.nthSeries n)

def Eseq (F : FormalGroup k) (n : ℕ) : MvPowerSeries (Fin 2) k :=
  MvPowerSeries.subst ![MvPowerSeries.X 0, useq F n] F.toPowerSeries
omit W in
theorem constantCoeff_useq (F : FormalGroup k) (n : ℕ) : MvPowerSeries.constantCoeff (useq F n) = 0 := by
  rw [useq, constantCoeff_emb]; exact F.constantCoeff_nthSeries n
omit W in
theorem useq_succ (F : FormalGroup k) (n : ℕ) :
    useq F (n + 1) = MvPowerSeries.subst ![useq F n, MvPowerSeries.X 1] F.toPowerSeries := by
  rw [useq, FormalGroup.nthSeries_succ, emb_subst_pair _ _ (F.constantCoeff_nthSeries n) PowerSeries.constantCoeff_X,
    emb_X]
  rfl
omit W in
theorem useq_one (F : FormalGroup k) : useq F 1 = MvPowerSeries.X 1 := by
  rw [useq, nthSeries_one, emb_X]
omit W in
theorem useq_eq_zero_iff (F : FormalGroup k) (n : ℕ) : useq F n = 0 ↔ F.nthSeries n = 0 := emb_eq_zero_iff _
omit W in
theorem constantCoeff_Eseq (F : FormalGroup k) (n : ℕ) : MvPowerSeries.constantCoeff (Eseq F n) = 0 :=
  WeierstrassCurve.kwB_constantCoeff_subst_pair (MvPowerSeries.constantCoeff_X 0) (constantCoeff_useq F n)
    F.zero_constantCoeff
omit W in
theorem Eseq_succ (F : FormalGroup k) (n : ℕ) :
    Eseq F (n + 1) = MvPowerSeries.subst ![Eseq F n, MvPowerSeries.X 1] F.toPowerSeries := by
  rw [Eseq, useq_succ, ← subst_pair_assoc F (MvPowerSeries.constantCoeff_X 0) (constantCoeff_useq F n)
    (MvPowerSeries.constantCoeff_X 1), Eseq]
omit W in
theorem Eseq_one (F : FormalGroup k) :
    Eseq F 1 = MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] F.toPowerSeries := by
  rw [Eseq, useq_one]
omit W in
theorem coeff_single0_useq (F : FormalGroup k) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (useq F n) = 0 := coeff_single_zero_emb _
omit W in
theorem coeff_single0_Eseq (F : FormalGroup k) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (Eseq F n) = 1 := by
  classical
  have hc0 : ∀ s : Fin 2, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, useq F n] : Fin 2 → MvPowerSeries (Fin 2) k) s) = 0 := by
    intro s; fin_cases s
    · exact MvPowerSeries.constantCoeff_X 0
    · exact constantCoeff_useq F n
  rw [Eseq, MvFormalGroup.coeff_single_subst hc0 F.toPowerSeries 0, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, F.lin_coeff_X, F.lin_coeff_Y,
    MvPowerSeries.coeff_index_single_self_X, coeff_single0_useq, one_mul, mul_zero, _root_.add_zero]
omit W in
theorem Eseq_ne_zero (F : FormalGroup k) (n : ℕ) : Eseq F n ≠ 0 := fun h => by
  have := coeff_single0_Eseq F n
  rw [h, map_zero] at this
  exact zero_ne_one this
omit W in
theorem Eseq_ne_X1 (F : FormalGroup k) (n : ℕ) : Eseq F n ≠ MvPowerSeries.X 1 := fun h => by
  classical
  have := coeff_single0_Eseq F n
  rw [h, MvPowerSeries.coeff_index_single_X] at this
  simp at this

theorem Z3_ne_zero {a b : MvPowerSeries (Fin 2) k} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (ha1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) a = 1)
    (hb0 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) b = 0) :
    (MvPowerSeries.subst ![a, b] W.fgZ3Fixed : MvPowerSeries (Fin 2) k) ≠ 0 := by
  classical
  intro h
  have hc0 : ∀ s : Fin 2, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → MvPowerSeries (Fin 2) k) s) = 0 := by
    intro s; fin_cases s
    · exact ha
    · exact hb
  have := MvFormalGroup.coeff_single_subst hc0 W.fgZ3Fixed 0
  rw [h, map_zero, Fin.sum_univ_two] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, W.coeff_single_fgZ3Fixed,
    ha1, hb0, mul_one, mul_zero, _root_.add_zero] at this
  norm_num at this
open Classical in

theorem genericPoint_Eseq (F : FormalGroup k) (hF : F.toPowerSeries = W.formalGroupLawFixed)
    (hw0 : WeierstrassCurve.genι (W.fgGenW (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) k)) ≠ 0)
    (hw1 : WeierstrassCurve.genι (W.fgGenW (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k)) ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) (hwE : WeierstrassCurve.genι (W.fgGenW (Eseq F n)) ≠ 0) :
    W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_Eseq F n)) hwE
      = W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)) hw0
        + n • W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)) hw1 := by
  classical
  induction n with
  | zero => exact absurd hn (by norm_num)
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      obtain ⟨hwF, hw0', hw1', hadd⟩ := W.exists_genericPoint_formalGroupLawFixed_eq_add
      have hE1 : Eseq F 1 = W.formalGroupLawFixed := by
        rw [Eseq_one, hF, MvPowerSeries.subst_X_pair_eq_self]
      rw [W.genericPoint_congr _ hwE (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalGroupLawFixed)
        hwF hE1, hadd, _root_.zero_add, one_smul]
    · have cE := constantCoeff_Eseq F m
      have cX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) = 0 :=
        MvPowerSeries.constantCoeff_X 1
      have hE : Eseq F (m + 1) = MvPowerSeries.subst ![Eseq F m, MvPowerSeries.X 1] W.formalGroupLawFixed := by
        rw [Eseq_succ, hF]
      have hwEm : WeierstrassCurve.genι (W.fgGenW (Eseq F m)) ≠ 0 :=
        W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cE) cE (Eseq_ne_zero F m)
      have cZ := WeierstrassCurve.kwB_constantCoeff_subst_pair cE cX1 W.constantCoeff_fgZ3Fixed
      have hwc : WeierstrassCurve.genι (W.fgGenW (MvPowerSeries.subst ![Eseq F m, MvPowerSeries.X 1] W.fgZ3Fixed)) ≠ 0 :=
        W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cZ) cZ
          (Z3_ne_zero W cE cX1 (coeff_single0_Eseq F m) (by
            classical
            rw [MvPowerSeries.coeff_index_single_X]; simp))
      have hwF' : WeierstrassCurve.genι (W.fgGenW (MvPowerSeries.subst ![Eseq F m, MvPowerSeries.X 1]
          W.formalGroupLawFixed)) ≠ 0 := by rw [← hE]; exact hwE
      have hx : W.xGen (Eseq F m) ≠ W.xGen (MvPowerSeries.X 1) :=
        W.xGen_ne hwEm hw1 (N_ne_zero W cE (coeff_single0_Eseq F m))
      have hhom := W.genericPoint_hom cE cX1 (Eseq_ne_X1 F m) hwEm hw1 hwc hwF' hx
      rw [W.genericPoint_congr _ hwE (PowerSeries.HasSubst.of_constantCoeff_zero
        (WeierstrassCurve.kwB_constantCoeff_subst_pair cE cX1 W.constantCoeff_formalGroupLawFixed)) hwF' hE,
        hhom, ih (by omega) hwEm, add_assoc, succ_nsmul]
end Main
end OBAux
namespace OBAux
open MvPowerSeries
noncomputable section Final

theorem ΨSq_natCast_ne_zero {k : Type} [Field k] (W : WeierstrassCurve k) [W.IsElliptic] (q : ℕ) [Fact q.Prime] :
    W.ΨSq (q : ℤ) ≠ 0 := by
  rw [WeierstrassCurve.ΨSq_ofNat]
  rcases (Fact.out : q.Prime).eq_two_or_odd' with h2 | hodd
  · subst h2
    rw [WeierstrassCurve.preΨ'_two, one_pow, one_mul, if_pos even_two]
    exact W.Psi2Sq_ne_zero_of_isElliptic
  · rw [if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one]
    exact pow_ne_zero 2 (W.prePsi_ne_zero_of_isElliptic hodd)
open Classical in

theorem orderBound (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (F : FormalGroup k) (hF : F.toPowerSeries = W.formalGroupLawFixed) :
    F.nthSeries q ≠ 0 ∧ ¬ (PowerSeries.X ^ (q * q + 1) ∣ F.nthSeries q) := by
  classical
  have hqp : q.Prime := Fact.out
  have hq1 : 1 ≤ q := hqp.one_lt.le
  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) k) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have cX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have nX0 : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) k) ≠ 0 := fun h => by
    simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
  have nX1 : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) ≠ 0 := fun h => by
    simpa [MvPowerSeries.coeff_X] using congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) h
  have hw0 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cX0) cX0 nX0
  have hw1 := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cX1) cX1 nX1
  set w1 : MvPowerSeries (Fin 2) k := W.fgGenW (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) with hw1def
  set x₁ : WeierstrassCurve.GenK (Fin 2) k := W.xGen (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) with hx₁
  set y₁ : WeierstrassCurve.GenK (Fin 2) k := W.yGen (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) with hy₁
  have hns := W.nonsingular_genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero cX1) hw1
  have hP1 : W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero cX1) hw1
      = WeierstrassCurve.Affine.Point.some x₁ y₁ hns := rfl
  have hx₁' : x₁ = WeierstrassCurve.genι (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k)
      / WeierstrassCurve.genι w1 := rfl
  have cEq := constantCoeff_Eseq F q
  have hwEq := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cEq) cEq (Eseq_ne_zero F q)
  have hgen := genericPoint_Eseq W F hF hw0 hw1 q hq1 hwEq
  set d : ℕ := q ^ 2 with hd
  set e : ℕ := (W.ΨSq (q : ℤ)).natDegree with he
  have hdΦ : (W.Φ (q : ℤ)).natDegree = d := by
    rw [WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast]
  have hed : e ≤ d - 1 := by
    have := W.natDegree_ΨSq_le (q : ℤ)
    rwa [Int.natAbs_natCast] at this
  have hd1 : 1 ≤ d := by rw [hd]; exact Nat.one_le_pow _ _ hq1
  have hΨ0 : W.ΨSq (q : ℤ) ≠ 0 := ΨSq_natCast_ne_zero W q
  have hΦ0 : W.Φ (q : ℤ) ≠ 0 := fun h => by
    have := W.coeff_Φ_ne_zero (q : ℤ)
    rw [h, Polynomial.coeff_zero] at this
    exact this rfl
  set HΦ₁ : PowerSeries k := homog₁ W (W.Φ (q : ℤ)) d with hHΦ₁
  set HΨ₁ : PowerSeries k := homog₁ W (W.ΨSq (q : ℤ)) d with hHΨ₁
  have oΦ : PowerSeries.order HΦ₁ = ((d : ℕ) : ℕ∞) := by
    rw [hHΦ₁, order_homog₁ W _ d hdΦ.le hΦ0, hdΦ]
    congr 1
    omega
  have oΨ : PowerSeries.order HΨ₁ = ((3 * d - 2 * e : ℕ) : ℕ∞) := by
    rw [hHΨ₁, order_homog₁ W _ d (by omega) hΨ0]
  have HΨ₁ne : HΨ₁ ≠ 0 := by
    intro h
    rw [h, PowerSeries.order_zero] at oΨ
    exact ENat.top_ne_coe _ oΨ
  have HΨne : homog (W.ΨSq (q : ℤ)) d (MvPowerSeries.X (1 : Fin 2)) w1 ≠ 0 := by
    rw [hw1def, ← emb_homog₁]
    exact fun h => HΨ₁ne ((emb_eq_zero_iff _).mp h)
  have hιHΨ : WeierstrassCurve.genι (homog (W.ΨSq (q : ℤ)) d (MvPowerSeries.X (1 : Fin 2)) w1) ≠ 0 := fun h =>
    HΨne ((map_eq_zero_iff WeierstrassCurve.genι
      (IsFractionRing.injective (MvPowerSeries (Fin 2) k) (WeierstrassCurve.GenK (Fin 2) k))).mp h)
  have evΦ := eval_homog (W.Φ (q : ℤ)) d hdΦ.le (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) w1 hw1
  have evΨ := eval_homog (W.ΨSq (q : ℤ)) d (by omega) (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) w1 hw1
  have hgenW : W.genW (Fin 2) = W.map (algebraMap k (WeierstrassCurve.GenK (Fin 2) k)) := rfl
  have evΦ' : ((W.genW (Fin 2)).Φ (q : ℤ)).eval x₁
      = WeierstrassCurve.genι (homog (W.Φ (q : ℤ)) d (MvPowerSeries.X (1 : Fin 2)) w1) / WeierstrassCurve.genι w1 ^ d := by
    rw [eq_div_iff (pow_ne_zero d hw1), mul_comm, hgenW, WeierstrassCurve.map_Φ, hx₁']
    exact evΦ
  have evΨ' : ((W.genW (Fin 2)).ΨSq (q : ℤ)).eval x₁
      = WeierstrassCurve.genι (homog (W.ΨSq (q : ℤ)) d (MvPowerSeries.X (1 : Fin 2)) w1) / WeierstrassCurve.genι w1 ^ d := by
    rw [eq_div_iff (pow_ne_zero d hw1), mul_comm, hgenW, WeierstrassCurve.map_ΨSq, hx₁']
    exact evΨ
  have hΨeval : ((W.genW (Fin 2)).ΨSq (q : ℤ)).eval x₁ ≠ 0 := by
    rw [evΨ']
    exact div_ne_zero hιHΨ (pow_ne_zero d hw1)
  haveI hEll : (W.genW (Fin 2)).IsElliptic := by rw [hgenW]; infer_instance
  have hψ : ((W.genW (Fin 2)).ψ (q : ℤ)).evalEval x₁ y₁ ≠ 0 := by
    intro h0
    have hsq := WeierstrassCurve.Affine.evalEval_psi_sq (W.genW (Fin 2))
      ((WeierstrassCurve.Affine.equation_iff_nonsingular).mpr hns) (q : ℤ)
    rw [h0, zero_pow two_ne_zero] at hsq
    exact hΨeval hsq.symm
  obtain ⟨y', h', hmul⟩ :=
    WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (W.genW (Fin 2)) hns (n := (q : ℤ)) hψ
  have hne : F.nthSeries q ≠ 0 := by
    intro hz
    have hu : useq F q = 0 := (useq_eq_zero_iff F q).mpr hz
    have hE : Eseq F q = MvPowerSeries.X 0 := by
      rw [Eseq, hu]; exact subst_pair_zero_right F cX0
    have h1 := hgen
    rw [W.genericPoint_congr _ hwEq (PowerSeries.HasSubst.of_constantCoeff_zero cX0) hw0 hE] at h1
    have h2 : (q : ℕ) • W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero cX1) hw1 = 0 :=
      left_eq_add.mp h1 |>.symm ▸ rfl
    rw [hP1, ← natCast_zsmul, hmul] at h2
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ h2
  refine ⟨hne, ?_⟩
  set r : ℕ := (F.nthSeries q).order.toNat with hr
  have hro : (F.nthSeries q).order = (r : ℕ∞) := (PowerSeries.coe_toNat_order hne).symm
  have hune : useq F q ≠ 0 := fun h => hne ((useq_eq_zero_iff F q).mp h)
  have cu := constantCoeff_useq F q
  have hwu := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cu) cu hune
  have hne0u : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) k) ≠ useq F q := fun h => by
    have := coeff_single0_useq F q
    rw [← h, MvPowerSeries.coeff_index_single_self_X] at this
    exact one_ne_zero this
  have cZ := WeierstrassCurve.kwB_constantCoeff_subst_pair cX0 cu W.constantCoeff_fgZ3Fixed
  have hwc := W.genι_fgGenW_ne_zero (PowerSeries.HasSubst.of_constantCoeff_zero cZ) cZ
    (Z3_ne_zero W cX0 cu (MvPowerSeries.coeff_index_single_self_X 0) (coeff_single0_useq F q))
  have hEq' : Eseq F q = MvPowerSeries.subst ![MvPowerSeries.X 0, useq F q] W.formalGroupLawFixed := by
    rw [Eseq, hF]
  have cF := WeierstrassCurve.kwB_constantCoeff_subst_pair cX0 cu W.constantCoeff_formalGroupLawFixed
  have hwF' : WeierstrassCurve.genι (W.fgGenW
      (MvPowerSeries.subst ![MvPowerSeries.X 0, useq F q] W.formalGroupLawFixed)) ≠ 0 := by
    rw [← hEq']; exact hwEq
  have ow : PowerSeries.order (W.fgGenW (F.nthSeries q) : PowerSeries k) = ((3 * r : ℕ) : ℕ∞) := by
    rw [order_fgGenW_eq W _ (F.constantCoeff_nthSeries q), hro]
    norm_cast
  have hx : W.xGen (MvPowerSeries.X (0 : Fin 2)) ≠ W.xGen (useq F q) := by
    apply W.xGen_ne hw0 hwu
    intro h0
    have key := congrArg
      (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (3 * r))) h0
    rw [map_zero, map_sub] at key
    have t1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (3 * r))
        ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * W.fgGenW (useq F q))
        = PowerSeries.coeff (3 * r) (W.fgGenW (F.nthSeries q) : PowerSeries k) := by
      rw [WeierstrassCurve.coeff_mul_noVar_X (WeierstrassCurve.noVar_X (by decide))
        (fun j hj => by
          have : j = 0 := by omega
          subst this
          exact W.noVar_fgGenW (noVar_emb _) cu) (by decide) (3 * r)]
      rw [MvPowerSeries.coeff_index_single_self_X, one_mul, useq,
        ← emb_fgGenW W _ (F.constantCoeff_nthSeries q), coeff_emb]
    have t2 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) (3 * r))
        (useq F q * W.fgGenW (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)) = 0 := by
      rw [show useq F q * W.fgGenW (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k)
          = W.fgGenW (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * useq F q from mul_comm _ _,
        WeierstrassCurve.coeff_mul_noVar_X (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (W.noVar_fgGenW (WeierstrassCurve.noVar_X (by decide)) cX0)
          (fun j hj => by
            have : j = 0 := by omega
            subst this
            exact noVar_emb (F.nthSeries q)) (by decide) (3 * r)]
      rw [W.coeff_fgGenW_X 0 1, W.coeff_formalW_one, zero_mul]
    rw [t1, t2, sub_zero] at key
    exact (PowerSeries.order_eq_nat.mp ow).1 key
  have hhom := W.genericPoint_hom cX0 cu hne0u hw0 hwu hwc hwF' hx
  have h3 : W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero cu) hwu
      = (q : ℕ) • W.genericPoint (PowerSeries.HasSubst.of_constantCoeff_zero cX1) hw1 := by
    have := hgen
    rw [W.genericPoint_congr _ hwEq (PowerSeries.HasSubst.of_constantCoeff_zero cF) hwF' hEq', hhom] at this
    exact add_left_cancel this
  rw [hP1, ← natCast_zsmul, hmul] at h3
  have hxu : W.xGen (useq F q)
      = ((W.genW (Fin 2)).Φ (q : ℤ)).eval x₁ / ((W.genW (Fin 2)).ΨSq (q : ℤ)).eval x₁ := by
    have := h3
    unfold WeierstrassCurve.genericPoint at this
    rw [WeierstrassCurve.Affine.Point.some.injEq] at this
    exact this.1
  rw [evΦ', evΨ', div_div_div_cancel_right₀ (pow_ne_zero d hw1),
    show W.xGen (useq F q) = WeierstrassCurve.genι (useq F q) / WeierstrassCurve.genι (W.fgGenW (useq F q)) from rfl,
    div_eq_div_iff hwu hιHΨ, ← map_mul, ← map_mul] at hxu
  have hMS := IsFractionRing.injective (MvPowerSeries (Fin 2) k) (WeierstrassCurve.GenK (Fin 2) k) hxu
  have hPS : F.nthSeries q * HΨ₁ = HΦ₁ * W.fgGenW (F.nthSeries q) := by
    have h4 : emb (F.nthSeries q * HΨ₁ - HΦ₁ * W.fgGenW (F.nthSeries q)) = 0 := by
      rw [show emb (F.nthSeries q * HΨ₁ - HΦ₁ * W.fgGenW (F.nthSeries q))
          = PowerSeries.substAlgHom hasSubst_X1 (F.nthSeries q * HΨ₁ - HΦ₁ * W.fgGenW (F.nthSeries q)) by
            rw [PowerSeries.coe_substAlgHom],
        map_sub, map_mul, map_mul, PowerSeries.coe_substAlgHom]
      rw [show PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (F.nthSeries q) = useq F q
          from rfl,
        show PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) HΨ₁ = emb HΨ₁ from rfl,
        show PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) HΦ₁ = emb HΦ₁ from rfl,
        show PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (W.fgGenW (F.nthSeries q))
          = emb (W.fgGenW (F.nthSeries q)) from rfl,
        hHΨ₁, hHΦ₁, emb_homog₁, emb_homog₁, emb_fgGenW W _ (F.constantCoeff_nthSeries q), ← hw1def]
      rw [show emb (F.nthSeries q) = useq F q from rfl, hMS, sub_self]
    exact sub_eq_zero.mp ((emb_eq_zero_iff _).mp h4)
  have o := congrArg PowerSeries.order hPS
  rw [PowerSeries.order_mul, PowerSeries.order_mul, oΨ, oΦ, ow, hro] at o
  have o' : r + (3 * d - 2 * e) = d + 3 * r := by exact_mod_cast o
  have hr_le : r ≤ d := by omega
  intro hdvd
  rw [PowerSeries.X_pow_dvd_iff] at hdvd
  have hdq : d = q * q := by rw [hd, pow_two]
  exact (PowerSeries.order_eq_nat.mp hro).1 (hdvd r (by omega))
end Final
end OBAux

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (F : FormalGroup k) (hF : F.toPowerSeries = W.formalGroupLawFixed) :
    F.nthSeries q ≠ 0 ∧ ¬ (PowerSeries.X ^ (q * q + 1) ∣ F.nthSeries q) :=
  OBAux.orderBound q k W F hF

end S_WeierstrassCurve_nthSeries_ne_zero_and_not_X_pow_dvd_of_charP
end P2MW
export P2MW.S_WeierstrassCurve_nthSeries_ne_zero_and_not_X_pow_dvd_of_charP (solution)
