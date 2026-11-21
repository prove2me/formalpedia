-- Prove2me | solution 1 for OnlineTransportation1195.Main.nearest_garage_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:08:10.380945+00:00
-- url     : https://prove2.me/submissions/0ca32c08-c08b-4fb2-ac28-71997dcc0ed6

import Definitions.Def_OnlineTransportation1195_Main_OnlinePolicy

section
namespace OnlineTransportation1195.Dev.Near
open OnlineTransportation1195.Main OnlineTransportation1195.Main.TransportationInstance

variable {n : ℕ}

noncomputable def phi (I : TransportationInstance n) :
    Fin I.garages.card ≃o {x // x ∈ I.garages} := I.garages.orderIsoOfFin rfl

noncomputable def emb (I : TransportationInstance n) (i : Fin I.garages.card) : Fin n :=
  ((phi I i : {x // x ∈ I.garages}) : Fin n)

theorem emb_inj (I : TransportationInstance n) : Function.Injective (emb I) := by
  intro a b h
  exact (phi I).injective (Subtype.ext h)

noncomputable def J (I : TransportationInstance n) : TransportationInstance I.garages.card where
  metric := @MetricSpace.induced _ _ (emb I) (emb_inj I) I.metric
  garages := Finset.univ
  capacity := fun g => I.capacity (phi I g.1)

noncomputable def sigmaJI (I : TransportationInstance n) : (J I).Slot ≃ I.Slot :=
  Equiv.sigmaCongr
    ((Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)).trans (phi I).toEquiv)
    (fun _ => Equiv.refl _)

theorem k_eq (I : TransportationInstance n) : (J I).k = I.k :=
  Fintype.card_congr (sigmaJI I)

noncomputable def rho (I : TransportationInstance n) : Fin (J I).k ≃ Fin I.k :=
  (Fintype.equivFin (J I).Slot).symm.trans ((sigmaJI I).trans (Fintype.equivFin I.Slot))

theorem garage_rho (I : TransportationInstance n) (u : Fin (J I).k) :
    ((Fintype.equivFin I.Slot).symm (rho I u)).1.val =
      emb I (((Fintype.equivFin (J I).Slot).symm u).1.1) := by
  have : (Fintype.equivFin I.Slot).symm (rho I u) =
      sigmaJI I ((Fintype.equivFin (J I).Slot).symm u) :=
    Equiv.symm_apply_apply _ _
  rw [this]
  rfl


theorem opt_le_cost (I : TransportationInstance n) (r : I.Arrivals) (a : I.Assignment) :
    I.opt r ≤ I.cost r a := by
  unfold TransportationInstance.opt
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))

theorem exists_opt (I : TransportationInstance n) (r : I.Arrivals) :
    ∃ a, I.opt r = I.cost r a := by
  have h := Finset.min'_mem (Finset.univ.image (I.cost r))
    (Finset.image_nonempty.mpr ⟨Equiv.refl I.Time, Finset.mem_univ _⟩)
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
  exact ⟨a, ha.symm⟩

theorem garageOf_mem (I : TransportationInstance n) (a : I.Assignment) (t : I.Time) :
    I.garageOf a t ∈ I.garages :=
  ((Fintype.equivFin I.Slot).symm (a t)).1.property

noncomputable def gstar (I : TransportationInstance n) (hG : I.garages.Nonempty) (x : Fin n) :
    Fin n :=
  letI := I.metric
  Classical.choose (Finset.exists_min_image I.garages (fun g => dist x g) hG)

theorem gstar_spec (I : TransportationInstance n) (hG : I.garages.Nonempty) (x : Fin n) :
    letI := I.metric
    gstar I hG x ∈ I.garages ∧ ∀ g ∈ I.garages, dist x (gstar I hG x) ≤ dist x g := by
  letI := I.metric
  exact Classical.choose_spec (Finset.exists_min_image I.garages (fun g => dist x g) hG)

noncomputable def nu (I : TransportationInstance n) (hG : I.garages.Nonempty) (x : Fin n) :
    Fin I.garages.card :=
  (phi I).symm ⟨gstar I hG x, (gstar_spec I hG x).1⟩

theorem emb_nu (I : TransportationInstance n) (hG : I.garages.Nonempty) (x : Fin n) :
    emb I (nu I hG x) = gstar I hG x := by
  unfold emb nu
  simp

noncomputable def pol (I : TransportationInstance n) (hG : I.garages.Nonempty)
    (AJ : Policy (J I)) : Policy I := fun r =>
  (finCongr (k_eq I)).symm.trans
    ((AJ (fun u => nu I hG (r (finCongr (k_eq I) u)))).trans (rho I))

theorem garage_pol (I : TransportationInstance n) (hG : I.garages.Nonempty)
    (AJ : Policy (J I)) (r : I.Arrivals) (t : I.Time) :
    I.garageOf (pol I hG AJ r) t =
      emb I ((J I).garageOf (AJ (fun u => nu I hG (r (finCongr (k_eq I) u))))
        ((finCongr (k_eq I)).symm t)) := by
  unfold TransportationInstance.garageOf
  have := garage_rho I (AJ (fun u => nu I hG (r (finCongr (k_eq I) u)))
        ((finCongr (k_eq I)).symm t))
  exact this

theorem causal_pol (I : TransportationInstance n) (hG : I.garages.Nonempty)
    (AJ : Policy (J I)) (hc : IsCausal (J I) AJ) : IsCausal I (pol I hG AJ) := by
  intro r q t hrq
  rw [garage_pol, garage_pol]
  congr 1
  apply hc
  intro j hj
  show nu I hG (r _) = nu I hG (q _)
  rw [hrq]
  rw [← Fin.val_fin_le] at hj ⊢
  simp only [finCongr_apply, Fin.coe_cast, finCongr_symm] at hj ⊢
  simpa using hj


theorem comp_pol (I : TransportationInstance n) (hG : I.garages.Nonempty)
    (AJ : Policy (J I)) (ρf : ℝ) (hρ : 0 ≤ ρf) (hcomp : Competitive (J I) AJ ρf) :
    Competitive I (pol I hG AJ) (2 * ρf + 1) := by
  intro r
  letI := I.metric
  set c := finCongr (k_eq I) with hc
  set r' : (J I).Arrivals := fun u => nu I hG (r (c u)) with hr'
  set b := AJ r' with hb
  obtain ⟨a, ha⟩ := exists_opt I r
  set Dsum : ℝ := ∑ u, dist (r (c u)) (gstar I hG (r (c u))) with hD
  -- cost of J run, unfolded
  have hcostJ : ∀ b' : (J I).Assignment, (J I).cost r' b' =
      ∑ u, dist (emb I (nu I hG (r (c u)))) (emb I ((J I).garageOf b' u)) := fun b' => rfl
  have hcostI : ∀ a' : I.Assignment, I.cost r a' = ∑ t, dist (r t) (I.garageOf a' t) := fun a' => rfl
  have hreidx : ∀ F : I.Time → ℝ, ∑ u, F (c u) = ∑ t, F t := fun F => Equiv.sum_comp c F
  -- Step 1
  have h1 : I.cost r (pol I hG AJ r) = ∑ u, dist (r (c u)) (emb I ((J I).garageOf b u)) := by
    rw [hcostI, ← hreidx]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [garage_pol]
    simp [hc, hb, hr']
  have h2 : I.cost r (pol I hG AJ r) ≤ Dsum + (J I).cost r' b := by
    rw [h1, hcostJ, hD, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [← emb_nu I hG (r (c u))]
    exact dist_triangle _ _ _
  have h3 : (J I).cost r' b ≤ ρf * (J I).opt r' := hcomp r'
  -- optimal assignment of I lifted to J
  set bs : (J I).Assignment := c.trans (a.trans (rho I).symm) with hbs
  have hrho : ∀ u, rho I (bs u) = a (c u) := fun u => by simp [hbs]
  have hg : ∀ u, emb I ((J I).garageOf bs u) = I.garageOf a (c u) := by
    intro u
    have := garage_rho I (bs u)
    rw [hrho] at this
    exact this.symm
  have hcostA : I.cost r a = ∑ u, dist (r (c u)) (I.garageOf a (c u)) := by
    rw [hcostI, hreidx (fun t => dist (r t) (I.garageOf a t))]
  have h5 : Dsum ≤ I.opt r := by
    rw [ha, hcostA, hD]
    refine Finset.sum_le_sum fun u _ => ?_
    exact (gstar_spec I hG (r (c u))).2 _ (garageOf_mem I a (c u))
  have h4 : (J I).opt r' ≤ Dsum + I.opt r := by
    refine (opt_le_cost (J I) r' bs).trans ?_
    rw [hcostJ, hD, ha, hcostA, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [hg, emb_nu]
    have h := dist_triangle (gstar I hG (r (c u))) (r (c u)) (I.garageOf a (c u))
    rw [dist_comm (gstar I hG (r (c u))) (r (c u))] at h
    exact h
  have h6 : ρf * (J I).opt r' ≤ ρf * (Dsum + I.opt r) := mul_le_mul_of_nonneg_left h4 hρ
  have h7 : ρf * Dsum ≤ ρf * I.opt r := mul_le_mul_of_nonneg_left h5 hρ
  nlinarith


theorem reduction_aux (f : ℕ → ℝ) (h : ∀ n : ℕ, PointRatio n (f n)) :
    GarageRatios (fun m => 2 * f m + 1) := by
  refine ⟨fun m => by linarith [(h m).1], fun n I => ?_⟩
  by_cases hG : I.garages.Nonempty
  · obtain ⟨AJ, hc, hcomp⟩ := (h I.garages.card).2 (J I)
    exact ⟨pol I hG AJ, causal_pol I hG AJ hc, comp_pol I hG AJ _ (h _).1 hcomp⟩
  · have hempty : IsEmpty I.Time := by
      have : I.k = 0 := by
        unfold TransportationInstance.k
        rw [Fintype.card_eq_zero_iff]
        refine ⟨fun ⟨g, c⟩ => hG ⟨g.1, g.2⟩⟩
      rw [TransportationInstance.Time, this]
      infer_instance
    refine ⟨fun _ => Equiv.refl _, fun r q t _ => hempty.elim t, ?_⟩
    intro r
    obtain ⟨a, ha⟩ := exists_opt I r
    have hz : ∀ a', I.cost r a' = 0 := fun a' => by
      unfold TransportationInstance.cost
      exact Finset.sum_eq_zero fun t _ => hempty.elim t
    rw [hz, ha, hz]
    simp

end OnlineTransportation1195.Dev.Near

namespace OnlineTransportation1195.Main
theorem chk_nearest_garage_reduction (f : ℕ → ℝ)
    (h : ∀ n : ℕ, PointRatio n (f n)) :
    GarageRatios (fun m => 2 * f m + 1) :=
  OnlineTransportation1195.Dev.Near.reduction_aux f h
end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_nearest_garage_reduction := @OnlineTransportation1195.Main.chk_nearest_garage_reduction
