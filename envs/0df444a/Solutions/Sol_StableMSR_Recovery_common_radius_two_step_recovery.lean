-- Prove2me | solution 1 for StableMSR.Recovery.common_radius_two_step_recovery
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T21:38:14.699294+00:00
-- url     : https://prove2.me/submissions/954968bc-2f8d-4d7b-a3b7-9653a84a0e79

import Theorems.Thm_StableMSR_Recovery_center_separation
import Theorems.Thm_StableMSR_Recovery_intercluster_separation
open StableMSR.Recovery
set_option autoImplicit false
set_option maxHeartbeats 1350000
open scoped Classical

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ) (hgap : γ ≤ (γ-1)^2)
    (O : Partition n) (hO : Stable d k γ O) :
    ∃ u v : Point n, ∀ x y : Point n,
      (∃ C ∈ O, x ∈ C ∧ y ∈ C) ↔ ∃ z : Point n, d x z ≤ d u v ∧ d z y ≤ d u v := by
  classical
  obtain ⟨m,hm⟩ := hd
  letI : MetricSpace (Point n) := m
  have ds (x y) : d x y=d y x := by simpa only [hm] using dist_comm x y
  have dt (x y z) : d x z ≤ d x y+d y z := by simpa only [hm] using dist_triangle x y z
  have nn (x y) : 0≤d x y := by exact (hm x y) ▸ (dist_nonneg : 0≤dist x y)
  have self (x) : d x x=0 := by exact (hm x x) ▸ dist_self x
  have two : 2 ≤ γ := by
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr hγ) (sub_pos.mpr h)]
  have occ (x : Point n) : ∃ C ∈ O, x∈C := by
    have h : x∈O.biUnion id := hO.1.2.2.2 ▸ Finset.mem_univ x
    exact Finset.mem_biUnion.mp h
  have disj {C D : Cluster n} (hc : C∈O) (hd' : D∈O) (hne : C≠D) {x : Point n}
      (hx : x∈C) : x∉D := fun h => Finset.disjoint_left.mp (hO.1.2.2.1 hc hd' hne) hx h
  have centers (C : Cluster n) (hc : C∈O) :
      ∃ c : Point n, OptimalCenter d C c ∧ ∀ x∈C, d c x ≤ radius d C := by
    have ne := hO.1.2.1 C hc
    obtain ⟨c,hc',he⟩ := C.exists_mem_eq_inf' ne (eccentricity d C)
    have e : radius d C = eccentricity d C c := by simpa [radius,ne] using he
    refine ⟨c,⟨hc',e.symm⟩,?_⟩
    intro x hx
    rw [e,eccentricity,dif_pos ne]
    exact Finset.le_sup' _ hx
  have off {C D : Cluster n} (hC : C∈O) (hD : D∈O) (hne : C≠D)
      {x y : Point n} (hx : x∈C) (hy : y∈D) : (γ-1)*radius d C < d x y := by
    obtain ⟨c,hc,hb⟩ := centers C hC
    have h1 := (center_separation d ⟨m,hm⟩ k hk γ hγ O hO C hC c hc).1 y (disj hD hC hne.symm hy)
    linarith [dt c x y,hb x hx]
  have neO : O.Nonempty := Finset.card_pos.mp (by rw [hO.1.1];omega)
  obtain ⟨A,hA,hmax⟩ := O.exists_mem_eq_sup' neO (radius d)
  let R := radius d A
  have hR (C : Cluster n) (hc : C∈O) : radius d C ≤ R := (Finset.le_sup' (radius d) hc).trans_eq hmax
  obtain ⟨u,hu,hbu⟩ := centers A hA
  have neA := hO.1.2.1 A hA
  obtain ⟨v,hv,hev⟩ := A.exists_mem_eq_sup' neA (d u)
  have huv : d u v=R := by
    calc d u v = A.sup' neA (d u) := hev.symm
         _ = eccentricity d A u := by simp [eccentricity,neA]
         _ = R := hu.2
  have hpos : 0≤R := (nn u v).trans_eq huv
  have gap {C D : Cluster n} (hC : C∈O) (hD : D∈O) (hne : C≠D)
      {x y : Point n} (hx : x∈C) (hy : y∈D) : R < d x y := by
    have atA : R ≤ (γ-1)*R := by nlinarith [mul_nonneg (sub_nonneg.mpr two) hpos]
    by_cases ez : R=0
    · rw [ez]
      have exy : x≠y := by rintro rfl;exact disj hC hD hne hx hy
      exact (hm x y) ▸ dist_pos.mpr exy
    by_cases a : C=A
    · subst C;exact atA.trans_lt (off hA hD hne hx hy)
    by_cases b : D=A
    · subst D;rw [ds x y];exact atA.trans_lt (off hA hC hne.symm hy hx)
    have hns : 2 ≤ A.card := by
      by_contra! h
      have one : A.card=1 := by have := Finset.card_pos.mpr neA;omega
      obtain ⟨p,he⟩ := Finset.card_eq_one.mp one
      have eu : u=p := by have hu' := hu.1;simpa [he] using hu'
      have ev : v=p := by simpa [he] using hv
      exact ez (huv.symm.trans (by rw [eu,ev,self]))
    have hh := intercluster_separation d ⟨m,hm⟩ k hk γ hγ O hO A C D hA hC hD (Ne.symm a) (Ne.symm b) hne hns
    have hxy : setDistance d C D ≤ (d x y : EReal) := sInf_le ⟨x,hx,y,hy,rfl⟩
    have he : (γ-1)*R < d x y + min (radius d C) (radius d D) := by
      have H := hh.trans_le (add_le_add_left hxy _)
      have cm : ((min (radius d C) (radius d D) : ℝ) : EReal) =
          min (radius d C : EReal) (radius d D : EReal) := by
        rcases le_total (radius d C) (radius d D) with h|h
        · rw [min_eq_left h,min_eq_left (EReal.coe_le_coe_iff.mpr h)]
        · rw [min_eq_right h,min_eq_right (EReal.coe_le_coe_iff.mpr h)]
      apply EReal.coe_lt_coe_iff.mp
      simpa only [R,EReal.coe_add,EReal.coe_sub,EReal.coe_one,EReal.coe_mul,cm] using H
    have hmin : (γ-1)*min (radius d C) (radius d D) < d x y :=
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)).trans_lt (off hC hD hne hx hy)
    have hh' := mul_lt_mul_of_pos_left he (sub_pos.mpr hγ)
    have hgap' := mul_le_mul_of_nonneg_right hgap hpos
    have hdxy : γ*R < γ*d x y := by nlinarith
    exact (mul_lt_mul_iff_right₀ (by linarith : 0<γ)).mp hdxy
  refine ⟨u,v,fun x y => ?_⟩
  rw [huv]
  constructor
  · rintro ⟨C,hC,hx,hy⟩
    obtain ⟨c,_,hc⟩ := centers C hC
    exact ⟨c,(ds x c) ▸ (hc x hx).trans (hR C hC),(hc y hy).trans (hR C hC)⟩
  · rintro ⟨z,hxz,hzy⟩
    obtain ⟨C,hC,hx⟩ := occ x
    obtain ⟨D,hD,hz⟩ := occ z
    obtain ⟨E,hE,hy⟩ := occ y
    have CD : C=D := by by_contra h;exact (not_lt_of_ge hxz) (gap hC hD h hx hz)
    have DE : D=E := by by_contra h;exact (not_lt_of_ge hzy) (gap hD hE h hz hy)
    exact ⟨C,hC,hx,(CD.trans DE).symm ▸ hy⟩
