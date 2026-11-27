-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceCoefficientsHolomorphic_proof_a4020852066e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:56:06.503494+00:00
-- url     : https://prove2.me/submissions/322767ca-fed6-4a01-9977-091c2ff25ea5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceCoefficientsHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_finset_prod_differentiableAt_085abbefa066
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_coeff_X_sub_C_differentiableAt_26a00f44276f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PieceCoefficientsHolomorphic
theorem _root_.solution : PieceCoefficientsHolomorphic.Statement := by
  classical
  intro n d N A Z c Q O F hcov hO hF hXOF i y₀ hy₀
  have hy₀' : eval y₀ Q ≠ 0 := hy₀
  obtain ⟨hfin, hcard, hsec⟩ := hcov y₀ hy₀'
  choose! U V g hU hyU hV hxV hg hgy hAg hZV using hsec
  set T : Finset (Fin n → ℂ) := hfin.toFinset with hT
  have hmemT : ∀ x, x ∈ T ↔ x ∈ Z ∧ A *ᵥ x = y₀ := fun x => by simp [T]
  have hTcard : T.card = N := by rw [← hcard, Set.ncard_eq_toFinset_card _ hfin]
  have hgd : ∀ x ∈ T, DifferentiableAt ℂ (g x) y₀ := fun x hx =>
    (hg x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).differentiableAt
      ((hU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).mem_nhds
        (hyU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2))
  have hgc : ∀ x ∈ T, Tendsto (g x) (𝓝 y₀) (𝓝 x) := fun x hx => by
    have := (hgd x hx).continuousAt
    rw [ContinuousAt, hgy x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2] at this
    exact this
  have hQopen : IsOpen {y : Fin d → ℂ | eval y Q ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval Q) continuous_const
  have hev : ∀ᶠ w in 𝓝 y₀, eval w Q ≠ 0 ∧ (∀ x ∈ T, w ∈ U x) ∧
      (∀ x ∈ T, ∀ x' ∈ T, x ≠ x' → g x w ≠ g x' w) ∧
      (∀ x ∈ T, x ∈ O → g x w ∈ O) ∧ (∀ x ∈ T, x ∉ O → g x w ∉ F) := by
    refine Filter.Eventually.and (hQopen.mem_nhds hy₀') (Filter.Eventually.and ?_
      (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)))
    · exact (eventually_all_finset T).2 fun x hx =>
        (hU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).mem_nhds (hyU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2)
    · refine (eventually_all_finset T).2 fun x hx => (eventually_all_finset T).2 fun x' hx' => ?_
      by_cases hxx : x = x'
      · exact Filter.Eventually.of_forall fun w h => absurd hxx h
      · exact ((hgc x hx).prodMk_nhds (hgc x' hx')).eventually
          ((isOpen_ne_fun continuous_fst continuous_snd).eventually_mem
            (show (x, x') ∈ {p : (Fin n → ℂ) × (Fin n → ℂ) | p.1 ≠ p.2} from hxx)) |>.mono
          fun w hw _ => hw
    · refine (eventually_all_finset T).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · exact ((hgc x hx).eventually (hO.eventually_mem hxO)).mono fun w hw _ => hw
      · exact Filter.Eventually.of_forall fun w h => absurd h hxO
    · refine (eventually_all_finset T).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · exact Filter.Eventually.of_forall fun w h => absurd hxO h
      · have hxF : x ∉ F := by
          intro hxF
          have hX : x ∈ {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F :=
            ⟨⟨((hmemT x).1 hx).1, by rw [((hmemT x).1 hx).2]; exact hy₀'⟩, hxF⟩
          rw [← hXOF] at hX
          exact hxO hX.2
        exact ((hgc x hx).eventually (hF.isOpen_compl.eventually_mem hxF)).mono fun w hw _ => hw
  have heq : (fun y => (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i) =ᶠ[𝓝 y₀]
      (fun y => (∏ x ∈ T.filter (· ∈ O),
        (Polynomial.X - Polynomial.C (∑ j, c j * g x y j))).coeff i) := by
    filter_upwards [hev] with w ⟨hwQ, hwU, hwinj, hwO, hwF⟩
    have hinj : Set.InjOn (fun x => g x w) T := fun x hx x' hx' h => by
      by_contra hne
      exact hwinj x hx x' hx' hne h
    have hgZ : ∀ x ∈ T, g x w ∈ Z ∧ A *ᵥ g x w = w := fun x hx => by
      have h1 := ((hmemT x).1 hx).1
      have h2 := ((hmemT x).1 hx).2
      refine ⟨?_, hAg x h1 h2 w (hwU x hx)⟩
      have hmem : g x w ∈ g x '' U x := ⟨w, hwU x hx, rfl⟩
      rw [← hZV x h1 h2] at hmem
      exact hmem.1
    obtain ⟨hfinw, hcardw, -⟩ := hcov w hwQ
    have hfull : ((T.image fun x => g x w : Finset _) : Set (Fin n → ℂ)) =
        {x | x ∈ Z ∧ A *ᵥ x = w} := by
      apply Set.eq_of_subset_of_ncard_le _ _ hfinw
      · intro z hz
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact hgZ x hx
      · rw [hcardw, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hTcard]
    have hset : {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w} =
        (((T.filter (· ∈ O)).image fun x => g x w : Finset _) : Set (Fin n → ℂ)) := by
      ext z
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨hzZ, hzO, hzA⟩
        have hz : z ∈ ((T.image fun x => g x w : Finset _) : Set (Fin n → ℂ)) := by
          rw [hfull]; exact ⟨hzZ, hzA⟩
        simp only [Finset.mem_coe, Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        refine ⟨x, ⟨hx, ?_⟩, rfl⟩
        by_contra hxO
        have hX : g x w ∈ {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O :=
          ⟨⟨hzZ, by rw [hzA]; exact hwQ⟩, hzO⟩
        rw [hXOF] at hX
        exact hwF x hx hxO hX.2
      · rintro ⟨x, ⟨hx, hxO⟩, rfl⟩
        exact ⟨(hgZ x hx).1, hwO x hx hxO, (hgZ x hx).2⟩
    have key : (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))) =
        ∏ x ∈ T.filter (· ∈ O), (Polynomial.X - Polynomial.C (∑ j, c j * g x w j)) := by
      rw [hset, finprod_mem_coe_finset, Finset.prod_image
        (fun x hx x' hx' h => hinj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx').1 h)]
    exact congrArg (fun p => Polynomial.coeff p i) key
  have hd : DifferentiableAt ℂ (fun y => (∏ x ∈ T.filter (· ∈ O),
      (Polynomial.X - Polynomial.C (∑ j, c j * g x y j))).coeff i) y₀ :=
    coeff_finset_prod_differentiableAt _ _ _ (fun x hx k => coeff_X_sub_C_differentiableAt _ _
      (DifferentiableAt.fun_sum fun j _ =>
        (differentiableAt_pi.1 (hgd x (Finset.mem_filter.1 hx).1) j).const_mul (c j)) k) i
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
end PieceCoefficientsHolomorphic
end GroundTheory.Heights₂.Heights.HilbertSamuel
