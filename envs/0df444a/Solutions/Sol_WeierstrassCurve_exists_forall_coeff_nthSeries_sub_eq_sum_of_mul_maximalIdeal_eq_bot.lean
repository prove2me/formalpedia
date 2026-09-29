-- Prove2me | solution 1 for WeierstrassCurve.exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a3e219cc-86f4-50c5-a0f4-235709ae55dc

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace FOPQAux

theorem main (q : ℕ) (k : Type) [Field k] (E₀ : WeierstrassCurve k) [E₀.IsElliptic]
    (A : Type) [CommRing A] [IsDomain A] (WA : WeierstrassCurve A) [WA.IsElliptic]
    (huniv : ∀ (S : Type) [CommRing S] (W : WeierstrassCurve S), IsUnit W.Δ → ∃ φ : A →+* S, WA.map φ = W)
    (huniq : ∀ (S : Type) [CommRing S] (φ₁ φ₂ : A →+* S), WA.map φ₁ = WA.map φ₂ → φ₁ = φ₂) :
    ∃ c : Fin 5 → k,
      ∀ (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T), I * maximalIdeal T = ⊥ → I ≤ maximalIdeal T →
      ∀ (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
      ∀ (E E' : WeierstrassCurve T), E.map resT = E₀ → E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) →
      ∀ (G G' : FormalGroup T), G.toPowerSeries = E.formalGroupLawFixed → G'.toPowerSeries = E'.formalGroupLawFixed →
      ∀ (t : Fin 5 → T), (∀ i, resT (t i) = c i) →
        PowerSeries.coeff q (G'.nthSeries q) - PowerSeries.coeff q (G.nthSeries q) =
          t 0 * (E'.a₁ - E.a₁) + t 1 * (E'.a₂ - E.a₂) + t 2 * (E'.a₃ - E.a₃) + t 3 * (E'.a₄ - E.a₄) +
            t 4 * (E'.a₆ - E.a₆) := by
  classical

  let U := TrivSqZeroExt A (Fin 5 → A)
  let Eu : WeierstrassCurve U :=
    ⟨TrivSqZeroExt.inl WA.a₁ + TrivSqZeroExt.inr (Pi.single 0 1),
     TrivSqZeroExt.inl WA.a₂ + TrivSqZeroExt.inr (Pi.single 1 1),
     TrivSqZeroExt.inl WA.a₃ + TrivSqZeroExt.inr (Pi.single 2 1),
     TrivSqZeroExt.inl WA.a₄ + TrivSqZeroExt.inr (Pi.single 3 1),
     TrivSqZeroExt.inl WA.a₆ + TrivSqZeroExt.inr (Pi.single 4 1)⟩
  let fstU : U →+* A := (TrivSqZeroExt.fstHom A A (Fin 5 → A)).toRingHom
  have hfstU : ∀ (a : A) (m : Fin 5 → A), fstU (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m) = a := by
    intro a m
    show TrivSqZeroExt.fst (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m : U) = a
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero]
  have hEufst : Eu.map fstU = WA := WeierstrassCurve.ext (hfstU _ _) (hfstU _ _) (hfstU _ _) (hfstU _ _) (hfstU _ _)
  have hΔU : IsUnit Eu.Δ := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, show TrivSqZeroExt.fst Eu.Δ = fstU Eu.Δ from rfl,
      ← WeierstrassCurve.map_Δ, hEufst]
    exact WA.isUnit_Δ

  obtain ⟨χ, hWAχ⟩ := huniv U Eu hΔU
  have hfstχ : fstU.comp χ = RingHom.id A := by
    apply huniq
    rw [← WeierstrassCurve.map_map, hWAχ, hEufst, WeierstrassCurve.map_id]
  set GU : FormalGroup U := WA.formalGroup.map χ with hGU
  have hGUser : GU.toPowerSeries = Eu.formalGroupLawFixed := by
    rw [hGU, FormalGroup.map_toPowerSeries, ← hWAχ, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map WA χ).2]; rfl
  have hbcU : GU.IsBaseChange fstU WA.formalGroup := by
    show WA.formalGroup.toPowerSeries = MvPowerSeries.map fstU GU.toPowerSeries
    rw [hGU, FormalGroup.map_toPowerSeries, MvPowerSeries.map_map, hfstχ, MvPowerSeries.map_id]; rfl
  set Pu : U := PowerSeries.coeff q (GU.nthSeries q) with hPu
  have hPufst : TrivSqZeroExt.fst Pu = PowerSeries.coeff q (WA.formalGroup.nthSeries q) := by
    rw [hPu, show TrivSqZeroExt.fst (PowerSeries.coeff q (GU.nthSeries q)) =
      fstU (PowerSeries.coeff q (GU.nthSeries q)) from rfl, ← PowerSeries.coeff_map,
      ← FormalGroup.IsBaseChange.nthSeries_eq_map _ _ _ hbcU q]

  obtain ⟨ψk, hψk⟩ := huniv k E₀ E₀.isUnit_Δ
  refine ⟨fun i => ψk (Pu.snd i), ?_⟩
  intro T _ _ I hI hIm resT hres hkerT E E' hE hEE' G G' hG hG' t ht
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hkerT, RingHom.mem_ker]
  have hImul : ∀ a b : T, a ∈ I → b ∈ maximalIdeal T → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ I * maximalIdeal T := Ideal.mul_mem_mul ha hb
    rwa [hI, Ideal.mem_bot] at this

  let δ : Fin 5 → T := ![E'.a₁ - E.a₁, E'.a₂ - E.a₂, E'.a₃ - E.a₃, E'.a₄ - E.a₄, E'.a₆ - E.a₆]
  have hδI : ∀ i, δ i ∈ I := by
    obtain ⟨e1, e2, e3, e4, e6⟩ := WeierstrassCurve.ext_iff.mp hEE'
    have hq : ∀ x y : T, Ideal.Quotient.mk I x = Ideal.Quotient.mk I y → x - y ∈ I := fun x y h =>
      (Ideal.Quotient.eq).mp h
    intro i; fin_cases i
    · exact hq _ _ e1
    · exact hq _ _ e2
    · exact hq _ _ e3
    · exact hq _ _ e4
    · exact hq _ _ e6

  have hEΔ : IsUnit E.Δ := by
    by_contra hu
    have hm : E.Δ ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [hmem, ← WeierstrassCurve.map_Δ, hE] at hm
    exact E₀.isUnit_Δ.ne_zero hm
  obtain ⟨φ, hWφ⟩ := huniv T E hEΔ
  have hresφ : ∀ a : A, resT (φ a) = ψk a := by
    have : resT.comp φ = ψk := huniq k _ _ (by rw [← WeierstrassCurve.map_map, hWφ, hE, hψk])
    intro a; exact congrFun (congrArg DFunLike.coe this) a

  let g : (Fin 5 → A) →ₗ[ℤ] T :=
    { toFun := fun m => ∑ i, φ (m i) * δ i
      map_add' := fun m m' => by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, map_add, add_mul]
      map_smul' := fun r m => by
        rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        show φ ((r • m) i) * δ i = r • (φ (m i) * δ i)
        rw [Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast, zsmul_eq_mul, mul_assoc] }
  have hg : ∀ m, g m = ∑ i, φ (m i) * δ i := fun m => rfl
  have hgg : ∀ x y, g x * g y = 0 := by
    intro x y
    rw [hg, hg, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have : δ i * δ j = 0 := hImul _ _ (hδI i) (hIm (hδI j))
    calc φ (x i) * δ i * (φ (y j) * δ j) = φ (x i) * φ (y j) * (δ i * δ j) := by ring
      _ = 0 := by rw [this, mul_zero]
  let Φ : U →ₐ[ℤ] T := TrivSqZeroExt.lift φ.toIntAlgHom g hgg
    (fun r x => by
      rw [hg, hg, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.toIntAlgHom_apply, mul_assoc])
    (fun r x => by
      rw [hg, hg, Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [op_smul_eq_smul, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.toIntAlgHom_apply]; ring)
  have hΦapp : ∀ (a : A) (m : Fin 5 → A), Φ (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m) = φ a + ∑ i, φ (m i) * δ i := by
    intro a m
    rw [map_add, TrivSqZeroExt.lift_apply_inl, TrivSqZeroExt.lift_apply_inr, RingHom.toIntAlgHom_apply, hg]
  have hsingle : ∀ i : Fin 5, (∑ j, φ ((Pi.single i (1 : A) : Fin 5 → A) j) * δ j) = δ i := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, map_one, one_mul]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  obtain ⟨w1, w2, w3, w4, w6⟩ := WeierstrassCurve.ext_iff.mp hWφ
  have hEu' : Eu.map Φ.toRingHom = E' := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show Φ (TrivSqZeroExt.inl WA.a₁ + TrivSqZeroExt.inr (Pi.single 0 1)) = E'.a₁
      rw [hΦapp, hsingle]; show φ WA.a₁ + (E'.a₁ - E.a₁) = E'.a₁
      rw [show φ WA.a₁ = E.a₁ from w1]; ring
    · show Φ (TrivSqZeroExt.inl WA.a₂ + TrivSqZeroExt.inr (Pi.single 1 1)) = E'.a₂
      rw [hΦapp, hsingle]; show φ WA.a₂ + (E'.a₂ - E.a₂) = E'.a₂
      rw [show φ WA.a₂ = E.a₂ from w2]; ring
    · show Φ (TrivSqZeroExt.inl WA.a₃ + TrivSqZeroExt.inr (Pi.single 2 1)) = E'.a₃
      rw [hΦapp, hsingle]; show φ WA.a₃ + (E'.a₃ - E.a₃) = E'.a₃
      rw [show φ WA.a₃ = E.a₃ from w3]; ring
    · show Φ (TrivSqZeroExt.inl WA.a₄ + TrivSqZeroExt.inr (Pi.single 3 1)) = E'.a₄
      rw [hΦapp, hsingle]; show φ WA.a₄ + (E'.a₄ - E.a₄) = E'.a₄
      rw [show φ WA.a₄ = E.a₄ from w4]; ring
    · show Φ (TrivSqZeroExt.inl WA.a₆ + TrivSqZeroExt.inr (Pi.single 4 1)) = E'.a₆
      rw [hΦapp, hsingle]; show φ WA.a₆ + (E'.a₆ - E.a₆) = E'.a₆
      rw [show φ WA.a₆ = E.a₆ from w6]; ring

  have hbc : WA.formalGroup.IsBaseChange φ G := by
    show G.toPowerSeries = MvPowerSeries.map φ WA.formalGroupLawFixed
    rw [hG, ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map WA φ).2, hWφ]
  have hbc' : GU.IsBaseChange Φ.toRingHom G' := by
    show G'.toPowerSeries = MvPowerSeries.map Φ.toRingHom GU.toPowerSeries
    rw [hG', hGUser, ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map Eu Φ.toRingHom).2, hEu']
  have hcoefG : PowerSeries.coeff q (G.nthSeries q) = φ Pu.fst := by
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map _ _ _ hbc q, PowerSeries.coeff_map, hPufst]
  have hcoefG' : PowerSeries.coeff q (G'.nthSeries q) = φ Pu.fst + ∑ i, φ (Pu.snd i) * δ i := by
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map _ _ _ hbc' q, PowerSeries.coeff_map, ← hPu]
    show Φ Pu = _
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq Pu]
    rw [hΦapp]

  have hdiff : ∀ i, (t i - φ (Pu.snd i)) * δ i = 0 := by
    intro i
    rw [mul_comm]
    refine hImul _ _ (hδI i) ?_
    rw [hmem, map_sub, ht, hresφ, sub_self]
  rw [hcoefG', hcoefG, add_sub_cancel_left]
  have hsum : ∑ i, t i * δ i = ∑ i, φ (Pu.snd i) * δ i := by
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← sub_mul]; exact hdiff i
  rw [← hsum, Fin.sum_univ_five]
  rfl

end FOPQAux

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (E₀ : WeierstrassCurve k) [E₀.IsElliptic] :
    ∃ c : Fin 5 → k,
      ∀ (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T), I * maximalIdeal T = ⊥ → I ≤ maximalIdeal T →
      ∀ (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
      ∀ (E E' : WeierstrassCurve T), E.map resT = E₀ → E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) →
      ∀ (G G' : FormalGroup T), G.toPowerSeries = E.formalGroupLawFixed → G'.toPowerSeries = E'.formalGroupLawFixed →
      ∀ (t : Fin 5 → T), (∀ i, resT (t i) = c i) →
        PowerSeries.coeff q (G'.nthSeries q) - PowerSeries.coeff q (G.nthSeries q) =
          t 0 * (E'.a₁ - E.a₁) + t 1 * (E'.a₂ - E.a₂) + t 2 * (E'.a₃ - E.a₃) + t 3 * (E'.a₄ - E.a₄) +
            t 4 * (E'.a₆ - E.a₆) := by
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
  have huniv : ∀ (S : Type) [CommRing S] (W : WeierstrassCurve S), IsUnit W.Δ → ∃ φ : A →+* S, WA.map φ = W := by
    intro S _ W hW
    let φ₀ : P →+* S := MvPolynomial.eval₂Hom (Int.castRingHom S) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
    have hφ₀W : Wu.map φ₀ = W := by
      refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
      · show MvPolynomial.eval₂Hom (Int.castRingHom S) _ (MvPolynomial.X _) = _
        rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
    have hφ₀Δ : IsUnit (φ₀ D) := by rw [← hD, ← WeierstrassCurve.map_Δ, hφ₀W]; exact hW
    refine ⟨IsLocalization.Away.lift D hφ₀Δ, ?_⟩
    rw [WeierstrassCurve.map_map, IsLocalization.Away.lift_comp, hφ₀W]
  have huniq : ∀ (S : Type) [CommRing S] (φ₁ φ₂ : A →+* S), WA.map φ₁ = WA.map φ₂ → φ₁ = φ₂ := by
    intro S _ φ₁ φ₂ h
    apply IsLocalization.ringHom_ext (Submonoid.powers D)
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map] at h
    obtain ⟨e1, e2, e3, e4, e6⟩ := WeierstrassCurve.ext_iff.mp h
    have hCint : ∀ r : ℤ, (MvPolynomial.C r : P) = (r : P) := fun r => by
      rw [← map_intCast (MvPolynomial.C : ℤ →+* P) r, Int.cast_id]
    apply MvPolynomial.ringHom_ext
    · intro n; rw [hCint, map_intCast, map_intCast]
    · intro i
      fin_cases i
      · exact e1
      · exact e2
      · exact e3
      · exact e4
      · exact e6
  exact FOPQAux.main q k E₀ A WA huniv huniq

end S_WeierstrassCurve_exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot
end P2MW
export P2MW.S_WeierstrassCurve_exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot (solution)
