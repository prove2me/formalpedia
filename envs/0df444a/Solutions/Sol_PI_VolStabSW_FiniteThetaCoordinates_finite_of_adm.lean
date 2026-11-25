-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.finite_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:42:20.334856+00:00
-- url     : https://prove2.me/submissions/fdba0d9d-5f78-436e-a748-dbe790fe8233

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_crd_map
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_crd_incl
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_crd_mulVec_le
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_crd_mulVec_le_one
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_exists_bound_crd
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_le_one_iff_mem
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_eventually_piV_le_one
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_continuous_piW_inf
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_piW_algebraMap
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_piV_algebraMap
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_finite_bdd
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_le_triple_sum_of_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution {M a : ℕ} (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsAdm F E Φ)
    (g : GL (Fin M) (AF F ⊗[F] E)) :
    {X : Fin a → Fin M → E | Φ (actTup (AF F) g (ratTup (AF F) X)) ≠ 0}.Finite := by
  classical
  obtain ⟨d, b, Φinf, Φf, Φv, _hcont, hcs, ⟨hSB, hae, hprod⟩, hIF⟩ := hΦ
  set m : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((g⁻¹ : GL (Fin M) (AF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hm
  set gm : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := ((g : GL (Fin M) (AF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) with hgm
  set Y : (Fin a → Fin M → E) → Fin a → Fin M → AF F ⊗[F] E :=
    fun X => actTup (AF F) g (ratTup (AF F) X) with hY
  set cst : Fin d → Fin d → Fin d → AF F := fun p q k => algebraMap F (AF F) (b.repr (b p * b q) k)
  have hback : ∀ X i, ratTup (AF F) X i = m.mulVec (Y X i) := by
    intro X i
    simp only [hY, actTup, Matrix.mulVec_mulVec, hm]
    rw [Units.inv_mul, Matrix.one_mulVec]
  have hx : ∀ X i j k, algebraMap F (AF F) (b.repr (X i j) k) = crd b (AF F) ((m.mulVec (Y X i)) j) k := by
    intro X i j k
    rw [← hback]
    exact (crd_incl b (AF F) (X i j) k).symm

  have hinfB : ∀ w : InfinitePlace F, ∃ B, 0 ≤ B ∧ ∀ Z ∈ tsupport Φinf, ∀ i j k,
      ‖(Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w).toRingHom (crd b (Ainf F) (Z i j) k)‖ ≤ B :=
    fun w => exists_bound_crd b _ (continuous_piW_inf F w) hcs
  choose Bw hBw0 hBw using hinfB

  have hfinB : ∀ v : HeightOneSpectrum (𝓞 F), ∃ B, 0 ≤ B ∧ ∀ Z ∈ tsupport (Φv v), ∀ i j k,
      ‖(RingHom.id (Fv F v)) (crd b (Fv F v) (Z i j) k)‖ ≤ B :=
    fun v => exists_bound_crd b _ continuous_id (hSB v).2
  choose Bv hBv0 hBv using hfinB

  have hgood : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 ∧
      (∀ i j p, ‖piV F v (crd b (AF F) (m i j) p)‖ ≤ 1) ∧ (∀ p q k, ‖piV F v (cst p q k)‖ ≤ 1) := by
    refine hae.and (Filter.Eventually.and ?_ ?_)
    · exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        Filter.eventually_all.2 fun p => eventually_piV_le_one F _
    · exact Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
        Filter.eventually_all.2 fun k => eventually_piV_le_one F _
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hgood).toFinset

  have hcV : ∀ (Z : Fin a → Fin M → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) i j k,
      crd b (Fv F v) (projV v (projFin Z) i j) k = piV F v (crd b (AF F) (Z i j) k) := by
    intro Z v i j k
    show crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (Z i j))) k = _
    rw [crd_map, crd_map]
    rfl
  have hcI : ∀ (Z : Fin a → Fin M → AF F ⊗[F] E) (w : InfinitePlace F) i j k,
      (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w).toRingHom
        (crd b (Ainf F) (projInf Z i j) k) = piW F w (crd b (AF F) (Z i j) k) := by
    intro Z w i j k
    show (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w)
        (crd b (Ainf F) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (Z i j)) k) = _
    rw [crd_map]
    rfl

  set Ci : InfinitePlace F → ℝ := fun w => M * (d * (d * (
    (∑ i, ∑ j, ∑ p, ‖piW F w (crd b (AF F) (m i j) p)‖) * Bw w *
    (∑ p, ∑ q, ∑ k, ‖piW F w (cst p q k)‖))))
  set Cv : HeightOneSpectrum (𝓞 F) → ℝ := fun v => M * (d * (d * (
    (∑ i, ∑ j, ∑ p, ‖piV F v (crd b (AF F) (m i j) p)‖) * Bv v *
    (∑ p, ∑ q, ∑ k, ‖piV F v (cst p q k)‖))))
  have hT := finite_bdd S Cv Ci
  set T := {x : F | (∀ v, ‖FinitePlace.embedding v x‖ ≤ Cv v) ∧
      (∀ v ∉ S, ‖FinitePlace.embedding v x‖ ≤ 1) ∧ ∀ w : InfinitePlace F, w x ≤ Ci w}
  have hT3 : (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin M =>
      Set.pi Set.univ fun _ : Fin d => T).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => hT
  have hinj : Function.Injective fun (X : Fin a → Fin M → E) (i : Fin a) (j : Fin M) (k : Fin d) =>
      b.repr (X i j) k := by
    intro X X' h
    funext i j
    exact b.repr.injective (Finsupp.ext fun k => congrFun (congrFun (congrFun h i) j) k)
  refine (hT3.preimage hinj.injOn).subset ?_
  intro X hX
  simp only [Set.mem_ofPred_eq] at hX
  have hne : Φ (Y X) ≠ 0 := hX
  rw [hIF] at hne
  have hne_inf := left_ne_zero_of_mul hne
  have hne_fin := right_ne_zero_of_mul hne

  have hYint : ∀ᶠ v in Filter.cofinite, ∀ i j k, ‖piV F v (crd b (AF F) (Y X i j) k)‖ ≤ 1 := by
    have h1 : ∀ᶠ v in Filter.cofinite, (∀ i j p, ‖piV F v (crd b (AF F) (gm i j) p)‖ ≤ 1) ∧
        (∀ i j q, ‖piV F v (crd b (AF F) (ratTup (AF F) X i j) q)‖ ≤ 1) ∧
        (∀ p q k, ‖piV F v (cst p q k)‖ ≤ 1) := by
      refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)
      · exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          Filter.eventually_all.2 fun p => eventually_piV_le_one F _
      · exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          Filter.eventually_all.2 fun p => eventually_piV_le_one F _
      · exact Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
          Filter.eventually_all.2 fun k => eventually_piV_le_one F _
    filter_upwards [h1] with v hv i j k
    exact norm_crd_mulVec_le_one b (piV F v).toRingHom gm (ratTup (AF F) X i) hv.1 (hv.2.1 i) hv.2.2 j k
  have hone : ∀ᶠ v in Filter.cofinite, Φv v (projV v (projFin (Y X))) = 1 := by
    filter_upwards [hYint, hae] with v hv hv'
    rw [hv']
    refine Set.indicator_of_mem ?_ _
    intro i j k
    rw [← norm_le_one_iff_mem]
    have := hv i j k
    rw [← hcV] at this
    exact this
  have hfin : (Function.mulSupport fun v => Φv v (projV v (projFin (Y X)))).Finite :=
    (Filter.eventually_cofinite.1 hone).subset fun v hv => hv
  have hall : ∀ v, Φv v (projV v (projFin (Y X))) ≠ 0 := by
    intro v
    rw [hprod, finprod_eq_prod _ hfin] at hne_fin
    by_cases hv : v ∈ hfin.toFinset
    · exact Finset.prod_ne_zero_iff.1 hne_fin v hv
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
      rw [hv]
      exact one_ne_zero
  intro i _ j _ k _
  refine ⟨?_, ?_, ?_⟩
  ·
    intro v
    rw [← norm_piV_algebraMap, hx]
    refine norm_crd_mulVec_le b (piV F v).toRingHom m (Y X i) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (hBv0 v)
      (fun i' j' p => le_triple_sum_of_nonneg (fun i' j' p => ‖piV F v (crd b (AF F) (m i' j') p)‖)
        (fun _ _ _ => norm_nonneg _) i' j' p)
      (fun j' q => ?_)
      (fun p q k' => le_triple_sum_of_nonneg (fun p q k' => ‖piV F v (cst p q k')‖) (fun _ _ _ => norm_nonneg _) p q k')
      j k
    have hmem := subset_tsupport _ (hall v)
    have := hBv v (projV v (projFin (Y X))) hmem i j' q
    rw [RingHom.id_apply, hcV] at this
    exact this
  ·
    intro v hv
    have hvS : v ∉ {v | ¬ (Φv v = (latV b v).indicator 1 ∧
        (∀ i j p, ‖piV F v (crd b (AF F) (m i j) p)‖ ≤ 1) ∧ (∀ p q k, ‖piV F v (cst p q k)‖ ≤ 1))} := by
      intro h
      exact hv ((Set.Finite.mem_toFinset _).2 h)
    simp only [Set.mem_ofPred_eq, not_not] at hvS
    obtain ⟨hΦv, hm1, hc1⟩ := hvS
    have hL : projV v (projFin (Y X)) ∈ latV b v := by
      by_contra hnot
      apply hall v
      rw [hΦv]
      exact Set.indicator_of_notMem hnot _
    rw [← norm_piV_algebraMap, hx]
    refine norm_crd_mulVec_le_one b (piV F v).toRingHom m (Y X i) hm1 (fun j' q => ?_) hc1 j k
    have := hL i j' q
    rw [← norm_le_one_iff_mem] at this
    show ‖piV F v (crd b (AF F) (Y X i j') q)‖ ≤ 1
    rw [← hcV]
    exact this
  ·
    intro w
    rw [← norm_piW_algebraMap, hx]
    refine norm_crd_mulVec_le b (piW F w).toRingHom m (Y X i) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (hBw0 w)
      (fun i' j' p => le_triple_sum_of_nonneg (fun i' j' p => ‖piW F w (crd b (AF F) (m i' j') p)‖)
        (fun _ _ _ => norm_nonneg _) i' j' p)
      (fun j' q => ?_)
      (fun p q k' => le_triple_sum_of_nonneg (fun p q k' => ‖piW F w (cst p q k')‖) (fun _ _ _ => norm_nonneg _) p q k')
      j k
    have hmem := subset_tsupport _ hne_inf
    have := hBw w (projInf (Y X)) hmem i j' q
    rw [hcI] at this
    exact this
end PI.VolStabSW.FiniteThetaCoordinates
