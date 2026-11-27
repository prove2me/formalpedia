-- Prove2me | solution 1 for ReserveLP.ProLPR.Supplement.theorem_3_corrected
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:22:39.44833+00:00
-- url     : https://prove2.me/submissions/b61c2049-8e36-4c4c-8a41-8325a5b71289

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Supplement_WeightedModel

open ReserveLP
open ReserveLP.ProLPR
open ReserveLP.ProLPR.Supplement

/-- Corrected limit formulation supported by the finite construction on pp. 18–19.
This changes both the printed coefficient and the finite-attainment quantifiers. -/
theorem solution (η : ℝ) (hη : 0 < η) :
    ∃ (m n : ℕ) (D : DataSet (Fin m) (Fin n)) (w : Fin m → ℝ)
      (s : Fin m → Profile (Fin n) → ℝ) (q : Fin n → ℝ → ℝ),
      (∀ a, 0 < w a) ∧ weightedLPOptimal D w s q ∧
      0 < weightedLPObj D w s ∧
      max (weightedRound D w q) (zeroRev D w) ≤
        ((1 + cStar)⁻¹ + η) * weightedLPObj D w s := by
          classical
          set_option maxHeartbeats 0 in
            set_option maxRecDepth 2048 in
              exact (open Finset in by
                let θ : ℝ := Real.sqrt 2 - 1
                have ht0 : 0 < θ := by dsimp [θ]; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
                have ht1 : θ < 1 := by dsimp [θ]; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
                have hcstar : cStar = (1 - θ ^ 2) * Real.exp (θ - 1) := by
                  dsimp [cStar, θ]
                  rw [show Real.sqrt 2 - 1 - 1 = Real.sqrt 2 - 2 by ring]
                  congr 1
                  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
                have hcstar0 : 0 < cStar := by rw [hcstar]; exact mul_pos (by nlinarith) (Real.exp_pos _)
                let C : ℕ → ℝ := fun k => (1 - (1 - θ) / k) ^ k * (1 - θ ^ 2)
                have hlim : Filter.Tendsto C Filter.atTop (nhds cStar) := by
                  have h := (Real.tendsto_one_add_div_pow_exp (θ - 1)).mul_const (1 - θ ^ 2)
                  have heq : C = (fun n : ℕ => (1 + (θ - 1) / n) ^ n * (1 - θ ^ 2)) := by
                    funext n
                    dsimp [C]
                    congr 2
                    ring
                  simpa only [heq, hcstar, mul_comm] using h
                have hlim' := hlim.const_add 1
                have hliminv := hlim'.inv₀ (ne_of_gt (by linarith : 0 < 1 + cStar))
                have hev : ∀ᶠ k : ℕ in Filter.atTop, (1 + C k)⁻¹ < (1 + cStar)⁻¹ + η :=
                  (tendsto_order.1 hliminv).2 _ (by linarith)
                obtain ⟨k, hkr⟩ := Filter.eventually_atTop.1 hev
                let K := max k 1
                have hK : 0 < K := by dsimp [K]; omega
                have hKreal : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
                have hratio : (1 + C K)⁻¹ < (1 + cStar)⁻¹ + η := hkr K (by dsimp [K]; omega)
                let α : ℝ := (1 - θ) / K
                have ha0 : 0 ≤ α := le_of_lt (div_pos (by linarith) (by exact_mod_cast hK))
                have ha1 : α < 1 := by
                  dsimp [α]
                  apply (div_lt_iff₀ (by exact_mod_cast hK : (0:ℝ) < K)).2
                  linarith
                have hamass : (K:ℝ) * α = 1 - θ := by
                  dsimp [α]; field_simp
                let c := C K
                have hc0 : 0 < c := by
                  dsimp [c, C]
                  exact mul_pos (pow_pos (by linarith : 0 < 1 - α) _) (by nlinarith)
                let sp : Fin 5 → (Fin (5 + K)) := Fin.castAdd K
                let rg : Fin K → (Fin (5 + K)) := Fin.natAdd 5
                let u : (Fin (5 + K)) := sp 0
                let v : (Fin (5 + K)) := sp 1
                let z : (Fin (5 + K)) := sp 2
                let d : (Fin (5 + K)) := sp 3
                let e : (Fin (5 + K)) := sp 4
                let β₀ : (Fin (5 + K)) → ℝ := Fin.addCases (fun j : Fin 5 => if j < 2 then 1 else 0) (fun _ => 1)
                let β₁ : (Fin (5 + K)) → ℝ := Fin.addCases (fun j : Fin 5 => if j = 2 then 2 else 0) (fun _ => 0)
                let D : DataSet (Fin 2) (Fin (5 + K)) := {
                  bid := fun a => if a = 0 then β₀ else β₁
                  bid_nonneg := by
                    intro a b
                    split_ifs <;> induction b using Fin.addCases <;> simp [β₀, β₁] <;> split_ifs <;> norm_num
                  b0 := d
                  b00 := e
                  b0_ne_b00 := by simp [d,e,sp,Fin.ext_iff]
                  bid_b0 := by intro a; split_ifs <;> simp [d,sp,β₀,β₁]
                  bid_b00 := by intro a; split_ifs <;> simp [e,sp,β₀,β₁] }
                have hbid0 : ∀ b, D.bid 0 b = β₀ b := by intro b; simp [D]
                have hbid1 : ∀ b, D.bid 1 b = β₁ b := by intro b; simp [D]
                have hR0 : (0:ℝ) ∈ reserves D := by simp [reserves]
                have hR1 : (1:ℝ) ∈ reserves D := by
                  apply Finset.mem_insert_of_mem
                  apply Finset.mem_insert_of_mem
                  exact Finset.mem_image.2 ⟨(0,u), mem_univ _, by simp [D,β₀,u,sp]⟩
                have hR2 : (2:ℝ) ∈ reserves D := by
                  apply Finset.mem_insert_of_mem
                  apply Finset.mem_insert_of_mem
                  exact Finset.mem_image.2 ⟨(1,z), mem_univ _, by simp [D,β₁,z,sp]⟩
                let P : Fin K → Profile (Fin (5 + K)) := fun i => (rg i, d, 1, 0)
                let T : Profile (Fin (5 + K)) := (u,v,0,0)
                let U : Profile (Fin (5 + K)) := (z,d,2,0)
                have hP : ∀ i, P i ∈ validProfiles D 0 := by
                  intro i
                  simp [validProfiles,P,hbid0,β₀,rg,d,sp, hR0,hR1, Fin.ext_iff]
                  omega
                have hT : T ∈ validProfiles D 0 := by
                  simp [validProfiles,T,hbid0,β₀,u,v,sp,hR0,Fin.ext_iff]
                have hU : U ∈ validProfiles D 1 := by
                  simp [validProfiles,U,hbid1,β₁,z,d,sp,hR0,hR2,Fin.ext_iff]
                let s₀ : Profile (Fin (5 + K)) → ℝ := fun p => (∑ i, if p = P i then α else 0) + if p = T then θ else 0
                let s₁ : Profile (Fin (5 + K)) → ℝ := fun p => if p = U then 1 else 0
                let s : Fin 2 → Profile (Fin (5 + K)) → ℝ := fun a => if a = 0 then s₀ else s₁
                let q : (Fin (5 + K)) → ℝ → ℝ := Fin.addCases
                  (fun j : Fin 5 => if j < 2 then (fun r => (if r = 0 then θ else 0) + if r = 2 then 1 - θ else 0)
                    else if j = 2 then (fun r => if r = 2 then 1 else 0)
                    else (fun r => if r = 0 then 1 else 0))
                  (fun _ r => (if r = 1 then α else 0) + if r = 2 then 1 - α else 0)
                have hqsum : ∀ b, ∑ r ∈ reserves D, q b r = 1 := by
                  intro b
                  induction b using Fin.addCases with
                  | left j =>
                    simp only [q, Fin.addCases_left]
                    split_ifs <;> simp [sum_add_distrib,hR0,hR1,hR2]
                  | right i => simp [q,sum_add_distrib,hR1,hR2]
                have hqnonneg : ∀ b r, 0 ≤ q b r := by
                  intro b r
                  induction b using Fin.addCases with
                  | left j => simp only [q,Fin.addCases_left]; split_ifs <;> dsimp only <;> split_ifs <;> linarith
                  | right i => simp only [q,Fin.addCases_right]; split_ifs <;> linarith
                have hs₀sum : ∀ (f : Profile (Fin (5 + K)) → ℝ),
                    (∑ p ∈ validProfiles D 0, s₀ p * f p) = α * ∑ i, f (P i) + θ * f T := by
                  intro f
                  simp only [s₀, add_mul, sum_add_distrib, sum_mul]
                  rw [Finset.sum_comm]
                  simp_rw [ite_mul, zero_mul]
                  simp [Finset.sum_ite_eq',hP,hT,← mul_sum]
                have hs₁sum : ∀ (f : Profile (Fin (5 + K)) → ℝ),
                    (∑ p ∈ validProfiles D 1, s₁ p * f p) = f U := by
                  intro f
                  simp [s₁,ite_mul,Finset.sum_ite_eq',hU]
                have hs0 : ∀ a p, 0 ≤ s a p := by
                  intro a p
                  dsimp [s]
                  split_ifs
                  · apply add_nonneg
                    · exact sum_nonneg (fun _ _ => by split_ifs <;> linarith)
                    · split_ifs <;> linarith
                  · dsimp [s₁]; split_ifs <;> norm_num
                have hsmass : ∀ a, ∑ p ∈ validProfiles D a, s a p ≤ 1 := by
                  intro a
                  fin_cases a
                  · have h := hs₀sum (fun _ => 1)
                    simp [s,hamass] at h ⊢
                    linarith
                  · have h := hs₁sum (fun _ => 1)
                    simpa [s] using h.le
                have hQ₀ : ∀ b r, (∑ p ∈ Qset D 0 b r, s₀ p) =
                    α * ∑ i, (if (d = b ∧ (0:ℝ) = r) ∨ (rg i = b ∧ (1:ℝ) = r) then 1 else 0) +
                    θ * (if (v = b ∧ (0:ℝ) = r) ∨ (u = b ∧ (0:ℝ) = r) then 1 else 0) := by
                  intro b r
                  have h := hs₀sum (fun p => if (p.2.1 = b ∧ p.2.2.2 = r) ∨ (p.1 = b ∧ p.2.2.1 = r) then 1 else 0)
                  simpa only [Qset, sum_filter, mul_ite, mul_one, mul_zero, P,T] using h
                have hQ₁ : ∀ b r, (∑ p ∈ Qset D 1 b r, s₁ p) =
                    (if (d = b ∧ (0:ℝ) = r) ∨ (z = b ∧ (2:ℝ) = r) then 1 else 0) := by
                  intro b r
                  have h := hs₁sum (fun p => if (p.2.1 = b ∧ p.2.2.2 = r) ∨ (p.1 = b ∧ p.2.2.1 = r) then 1 else 0)
                  simpa only [Qset, sum_filter, mul_ite, mul_one, mul_zero, U] using h
                have hsep : ∀ (j : Fin 5) (i : Fin K), sp j ≠ rg i := by
                  intro j i h
                  have h' := congrArg Fin.val h
                  dsimp [sp,rg] at h'
                  omega
                have hsep' : ∀ (i : Fin K) (j : Fin 5), rg i ≠ sp j := fun i j => (hsep j i).symm
                have hqmarg : ∀ a b r, ∑ p ∈ Qset D a b r, s a p ≤ q b r := by
                  intro a b r
                  fin_cases a
                  · change (∑ p ∈ Qset D 0 b r, s₀ p) ≤ q b r
                    rw [hQ₀]
                    induction b using Fin.addCases with
                    | left j =>
                      fin_cases j <;>
                        (by_cases hr0 : r = 0 <;> by_cases hr2 : r = 2 <;>
                        simp [q,d,u,v,sp,Fin.castAdd_inj,hsep',rg,hamass,hr0,hr2,eq_comm] <;> nlinarith [hamass])
                    | right i =>
                      by_cases hr1 : r = 1 <;> by_cases hr2 : r = 2 <;>
                        simp [q,rg,d,u,v,sp,hsep,Fin.natAdd_inj,hr1,hr2,eq_comm,Finset.sum_ite_eq'] <;> linarith
                  · change (∑ p ∈ Qset D 1 b r, s₁ p) ≤ q b r
                    rw [hQ₁]
                    induction b using Fin.addCases with
                    | left j =>
                      fin_cases j <;>
                        (by_cases hr0 : r = 0 <;> by_cases hr2 : r = 2 <;>
                        simp [q,d,z,sp,Fin.castAdd_inj,hr0,hr2,eq_comm] <;> linarith)
                    | right i =>
                      by_cases hr1 : r = 1 <;> by_cases hr2 : r = 2 <;>
                        simp [q,rg,d,z,sp,hsep,hr1,hr2] <;> linarith
                have hfeas : LPFeasible D s q :=
                  ⟨fun a p _ => hs0 a p, hsmass, fun a b r _ => hqmarg a b r, hqsum, fun b r _ => hqnonneg b r⟩
                let w : Fin 2 → ℝ := fun a => if a = 0 then 1 else c / 2
                have hw : ∀ a, 0 < w a := by intro a; fin_cases a <;> simp [w,hc0]
                have hcap₀ : ∀ b, D.bid 0 b ≤ 1 := by
                  intro b; rw [hbid0]
                  induction b using Fin.addCases <;> simp [β₀] <;> split_ifs <;> norm_num
                have hcap₁ : ∀ b, D.bid 1 b ≤ 2 := by
                  intro b; rw [hbid1]
                  induction b using Fin.addCases <;> simp [β₁] <;> split_ifs <;> norm_num
                have hcapP : ∀ a p, p ∈ validProfiles D a → revProfile D a p ≤ (if a = 0 then 1 else 2) := by
                  intro a p hp
                  have hh := (mem_filter.1 hp).2
                  apply max_le
                  · exact le_trans hh.2.1 (by fin_cases a; exact hcap₀ _; exact hcap₁ _)
                  · exact le_trans hh.2.2.1 (by fin_cases a; exact hcap₀ _; exact hcap₁ _)
                have hobj : weightedLPObj D w s = 1 + c := by
                  have h0 := hs₀sum (revProfile D 0)
                  have h1 := hs₁sum (revProfile D 1)
                  have hp : ∀ i, revProfile D 0 (P i) = 1 := by intro i; simp [revProfile,P,hbid0,β₀,rg,d,sp]
                  have ht : revProfile D 0 T = 1 := by simp [revProfile,T,hbid0,β₀,v,sp]
                  have hu : revProfile D 1 U = 2 := by simp [revProfile,U,hbid1,β₁,d,sp]
                  simp only [hp,ht,hu,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h0 h1
                  simp only [weightedLPObj,Fin.sum_univ_two,w,s,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,one_mul]
                  rw [h0,h1]
                  nlinarith only [hamass]
                have hopt : weightedLPOptimal D w s q := by
                  refine ⟨hfeas, ?_⟩
                  intro s' q' hf
                  rw [hobj]
                  have hh : ∀ a, (∑ p ∈ validProfiles D a, s' a p * revProfile D a p) ≤ (if a = 0 then 1 else 2) := by
                    intro a
                    calc
                      _ ≤ ∑ p ∈ validProfiles D a, s' a p * (if a = 0 then 1 else 2) :=
                        sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hcapP a p hp) (hf.1 a p hp))
                      _ = (∑ p ∈ validProfiles D a, s' a p) * (if a = 0 then 1 else 2) := by rw [sum_mul]
                      _ ≤ 1 * (if a = 0 then 1 else 2) := mul_le_mul_of_nonneg_right (hf.2.1 a) (by split_ifs <;> norm_num)
                      _ = _ := one_mul _
                  have h0 := hh 0
                  have h1 := hh 1
                  simp only [ite_true,show (1:Fin 2) ≠ 0 by decide,if_false] at h0 h1
                  simp only [weightedLPObj,Fin.sum_univ_two,w,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,one_mul]
                  calc
                    _ ≤ 1 + c / 2 * 2 := add_le_add h0 (mul_le_mul_of_nonneg_left h1 (by positivity))
                    _ = 1 + c := by ring
                have hrevle : ∀ a (ρ : Fin (5 + K) → ℝ) t, 0 ≤ t →
                    (∀ b ∈ cleared D a ρ, ρ b ≤ t) →
                    (∀ b ∈ cleared D a ρ, ∀ b' ∈ cleared D a ρ, b ≠ b' → min (D.bid a b) (D.bid a b') ≤ t) →
                    revA D a ρ ≤ t := by
                  intro a ρ t ht hr hb
                  unfold revA
                  split_ifs with hn
                  · apply (sup'_le_iff _ _).2
                    intro b hbb
                    simp only [topBidders, mem_filter] at hbb
                    obtain ⟨hbc,htop⟩ := hbb
                    apply max_le (hr b hbc)
                    apply (max'_le_iff _ _).2
                    intro x hx
                    rcases mem_insert.1 hx with hx | hx
                    · simpa [hx] using ht
                    · obtain ⟨b',hb',rfl⟩ := mem_image.1 hx
                      obtain ⟨hne,hb'c⟩ := mem_erase.1 hb'
                      have hmin := hb b' hb'c b hbc hne
                      simpa [min_eq_left (htop b' hb'c)] using hmin
                  · exact ht
                have hrevcap : ∀ a (ρ : Fin (5 + K) → ℝ) t, 0 ≤ t →
                    (∀ b, D.bid a b ≤ t) → revA D a ρ ≤ t := by
                  intro a ρ t ht hb
                  exact hrevle a ρ t ht
                    (fun b hc => le_trans (mem_filter.1 hc).2 (hb b))
                    (fun b _ b' _ _ => le_trans (min_le_left _ _) (hb b))
                have hrev0cap : ∀ ρ, revA D 0 ρ ≤ 1 := fun ρ => hrevcap 0 ρ 1 (by norm_num) hcap₀
                have hrev1cap : ∀ ρ, revA D 1 ρ ≤ 2 := fun ρ => hrevcap 1 ρ 2 (by norm_num) hcap₁
                have hzero1 : revA D 1 (fun _ => 0) ≤ 0 := by
                  apply hrevle 1 _ 0 (by rfl) (by intros; rfl)
                  intro b _ b' _ hne
                  have hz : ∀ b, D.bid 1 b = 0 ∨ b = z := by
                    intro b
                    induction b using Fin.addCases with
                    | left j =>
                      by_cases hj : j = 2
                      · right; subst j; rfl
                      · left; simp [hbid1,β₁,hj]
                    | right i => left; simp [hbid1,β₁]
                  rcases hz b with h | h
                  · exact (min_le_left _ _).trans (le_of_eq h)
                  · rcases hz b' with h' | h'
                    · exact (min_le_right _ _).trans (le_of_eq h')
                    · exact False.elim (hne (h.trans h'.symm))
                have hzero : zeroRev D w ≤ 1 := by
                  have h0 := hrev0cap (fun _ => 0)
                  unfold zeroRev weightedRev
                  simp only [Fin.sum_univ_two,w,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,one_mul]
                  have hh := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ c / 2 by positivity) hzero1
                  linarith only [h0,hh]
                have hfactor : ∀ (f : Fin (5 + K) → ℝ → ℝ),
                    (∑ ρ ∈ roundings D, roundProb q ρ * ∏ b, f b (ρ b)) =
                    ∏ b, ∑ r ∈ reserves D, q b r * f b r := by
                  intro f
                  simp only [roundProb,← prod_mul_distrib,roundings]
                  exact (Finset.prod_univ_sum (fun _ : Fin (5 + K) => reserves D) (fun b r => q b r * f b r)).symm
                have htotal : ∑ ρ ∈ roundings D, roundProb q ρ = 1 := by
                  have h := hfactor (fun _ _ => 1)
                  simpa [hqsum] using h
                let f : Fin (5 + K) → ℝ → ℝ := Fin.addCases (fun _ _ => 1) (fun _ r => if r = 2 then 1 else 0)
                let g : Fin (5 + K) → ℝ → ℝ := Fin.addCases
                    (fun j r => if j < 2 then (if r = 0 then 1 else 0) else 1)
                    (fun _ r => if r = 2 then 1 else 0)
                let F : (Fin (5 + K) → ℝ) → ℝ := fun ρ => ∏ b, f b (ρ b)
                let G : (Fin (5 + K) → ℝ) → ℝ := fun ρ => ∏ b, g b (ρ b)
                have hmeanF : (∑ ρ ∈ roundings D, roundProb q ρ * F ρ) = (1 - α)^K := by
                  rw [show (∑ ρ ∈ roundings D, roundProb q ρ * F ρ) = _ from hfactor f]
                  rw [Fin.prod_univ_add]
                  have hl : ∀ j : Fin 5, (∑ r ∈ reserves D, q (sp j) r * f (sp j) r) = 1 := by
                    intro j
                    simpa [f,sp] using hqsum (sp j)
                  have hr : ∀ i : Fin K, (∑ r ∈ reserves D, q (rg i) r * f (rg i) r) = 1 - α := by
                    intro i
                    simp [q,f,rg,mul_ite,Finset.sum_ite_eq',hR2]
                  simpa only [sp,rg] using (show (∏ j, (∑ r ∈ reserves D, q (sp j) r * f (sp j) r)) *
                    (∏ i, (∑ r ∈ reserves D, q (rg i) r * f (rg i) r)) = (1 - α)^K by simp [hl,hr])
                have hmeanG : (∑ ρ ∈ roundings D, roundProb q ρ * G ρ) = θ^2 * (1 - α)^K := by
                  rw [show (∑ ρ ∈ roundings D, roundProb q ρ * G ρ) = _ from hfactor g]
                  rw [Fin.prod_univ_add]
                  have hl : ∀ j : Fin 5, (∑ r ∈ reserves D, q (sp j) r * g (sp j) r) = if j < 2 then θ else 1 := by
                    intro j
                    by_cases hj : j < 2
                    · simp [q,g,sp,hj,mul_ite,Finset.sum_ite_eq',hR0]
                    · simpa [g,sp,hj] using hqsum (sp j)
                  have hr : ∀ i : Fin K, (∑ r ∈ reserves D, q (rg i) r * g (rg i) r) = 1 - α := by
                    intro i
                    simp [q,g,rg,mul_ite,Finset.sum_ite_eq',hR2]
                  simp only [← show sp = Fin.castAdd K from rfl, ← show rg = Fin.natAdd 5 from rfl]
                  simp only [hl,hr,prod_const,card_univ,Fintype.card_fin]
                  norm_num [Fin.prod_univ_succ,pow_two,Fin.lt_def]
                have hF : ∀ ρ, F ρ = if (∀ i, ρ (rg i) = 2) then 1 else 0 := by
                  intro ρ
                  simp [F,f,Fin.prod_univ_add,Finset.prod_boole,rg]
                have hG : ∀ ρ, G ρ = (if ρ u = 0 ∧ ρ v = 0 then 1 else 0) * F ρ := by
                  intro ρ
                  by_cases hu : ρ u = 0 <;> by_cases hv : ρ v = 0 <;>
                    simp [G,g,F,f,Fin.prod_univ_add,Fin.prod_univ_succ,Fin.lt_def,u,v,sp] at hu hv ⊢ <;>
                    simp [hu,hv]
                have hloss : ∀ ρ, F ρ - G ρ =
                    if (∀ i, ρ (rg i) = 2) ∧ ¬(ρ u = 0 ∧ ρ v = 0) then 1 else 0 := by
                  intro ρ
                  rw [hG,hF]
                  by_cases ha : (∀ i, ρ (rg i) = 2) <;>
                    by_cases hb : ρ u = 0 ∧ ρ v = 0 <;> simp [ha,hb]
                have hbadzero : ∀ ρ, (∀ b, q b (ρ b) ≠ 0) →
                    (∀ i, ρ (rg i) = 2) → ¬(ρ u = 0 ∧ ρ v = 0) → revA D 0 ρ ≤ 0 := by
                  intro ρ hsupport hall hnot
                  have hclear : ∀ b ∈ cleared D 0 ρ,
                      ρ b = 0 ∧ (b = u ∨ b = v ∨ D.bid 0 b = 0) := by
                    intro b hb
                    have hb' : ρ b ≤ D.bid 0 b := (mem_filter.1 hb).2
                    have hq := hsupport b
                    induction b using Fin.addCases with
                    | left j =>
                      fin_cases j
                      · have hb1 : ρ (sp 0) ≤ 1 := by simpa [sp,hbid0,β₀] using hb'
                        have hr : ρ (sp 0) = 0 := by
                          by_contra hn
                          have hn2 : ρ (sp 0) ≠ 2 := by linarith
                          have hh := hsupport (sp 0)
                          simpa [q,sp,hn,hn2] using hh
                        exact ⟨hr,Or.inl rfl⟩
                      · have hb1 : ρ (sp 1) ≤ 1 := by simpa [sp,hbid0,β₀] using hb'
                        have hr : ρ (sp 1) = 0 := by
                          by_contra hn
                          have hn2 : ρ (sp 1) ≠ 2 := by linarith
                          have hh := hsupport (sp 1)
                          simpa [q,sp,hn,hn2] using hh
                        exact ⟨hr,Or.inr (Or.inl rfl)⟩
                      · have hb1 : ρ (sp 2) ≤ 0 := by simpa [sp,hbid0,β₀] using hb'
                        have hn2 : ρ (sp 2) ≠ 2 := by linarith
                        have hh := hsupport (sp 2)
                        simp [q,sp,hn2] at hh
                      · have hr : ρ (sp 3) = 0 := by
                          by_contra hn
                          have hh := hsupport (sp 3)
                          simp [q,sp,hn] at hh
                        exact ⟨hr,Or.inr (Or.inr (by simp [hbid0,β₀,sp]))⟩
                      · have hr : ρ (sp 4) = 0 := by
                          by_contra hn
                          have hh := hsupport (sp 4)
                          simp [q,sp,hn] at hh
                        exact ⟨hr,Or.inr (Or.inr (by simp [hbid0,β₀,sp]))⟩
                    | right i =>
                      have hh := hall i
                      have hb1 : ρ (rg i) ≤ 1 := by simpa [rg,hbid0,β₀] using hb'
                      linarith
                  apply hrevle 0 ρ 0 (by rfl)
                  · intro b hb
                    exact le_of_eq (hclear b hb).1
                  · intro b hb b' hb' hne
                    obtain ⟨hr,hb⟩ := hclear b hb
                    obtain ⟨hr',hb'⟩ := hclear b' hb'
                    rcases hb with rfl | rfl | hb
                    · rcases hb' with rfl | rfl | hb'
                      · exact False.elim (hne rfl)
                      · exact False.elim (hnot ⟨hr,hr'⟩)
                      · exact (min_le_right _ _).trans (le_of_eq hb')
                    · rcases hb' with rfl | rfl | hb'
                      · exact False.elim (hnot ⟨hr',hr⟩)
                      · exact False.elim (hne rfl)
                      · exact (min_le_right _ _).trans (le_of_eq hb')
                    · exact (min_le_left _ _).trans (le_of_eq hb)
                have hpoint : ∀ ρ, roundProb q ρ * weightedRev D w ρ ≤
                    roundProb q ρ * (1 + c - F ρ + G ρ) := by
                  intro ρ
                  have hpn : 0 ≤ roundProb q ρ := prod_nonneg (fun b _ => hqnonneg b (ρ b))
                  by_cases hp : roundProb q ρ = 0
                  · simp [hp]
                  have hsupport : ∀ b, q b (ρ b) ≠ 0 := by
                    intro b
                    exact (prod_ne_zero_iff.1 hp) b (mem_univ _)
                  apply mul_le_mul_of_nonneg_left _ hpn
                  have h0 : revA D 0 ρ ≤ 1 - F ρ + G ρ := by
                    have hh := hloss ρ
                    by_cases hb : (∀ i, ρ (rg i) = 2) ∧ ¬(ρ u = 0 ∧ ρ v = 0)
                    · rw [if_pos hb] at hh
                      have hz := hbadzero ρ hsupport hb.1 hb.2
                      linarith
                    · rw [if_neg hb] at hh
                      have hz := hrev0cap ρ
                      linarith
                  have h1 := hrev1cap ρ
                  unfold weightedRev
                  simp only [Fin.sum_univ_two,w,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false,one_mul]
                  calc
                    _ ≤ (1 - F ρ + G ρ) + c / 2 * 2 :=
                      add_le_add h0 (mul_le_mul_of_nonneg_left h1 (by positivity))
                    _ = 1 + c - F ρ + G ρ := by ring
                have hround : weightedRound D w q ≤ 1 := by
                  calc
                    _ ≤ ∑ ρ ∈ roundings D, roundProb q ρ * (1 + c - F ρ + G ρ) := sum_le_sum (fun ρ _ => hpoint ρ)
                    _ = (1 + c) * (∑ ρ ∈ roundings D, roundProb q ρ) -
                        (∑ ρ ∈ roundings D, roundProb q ρ * F ρ) +
                        (∑ ρ ∈ roundings D, roundProb q ρ * G ρ) := by
                      simp only [mul_add,mul_sub,sum_add_distrib,sum_sub_distrib,← sum_mul]
                      ring
                    _ = 1 := by rw [htotal,hmeanF,hmeanG]; dsimp [c,C,α]; ring
                refine ⟨2,5+K,D,w,s,q,hw,hopt,?_,?_⟩
                · rw [hobj]; linarith
                · apply le_trans (max_le hround hzero)
                  rw [hobj]
                  have hpos : 0 < 1 + c := by linarith
                  have hh : (1 + c)⁻¹ ≤ (1 + cStar)⁻¹ + η := le_of_lt hratio
                  have hm := (mul_le_mul_of_nonneg_right hh hpos.le)
                  simpa only [inv_mul_cancel₀ (ne_of_gt hpos)] using hm
              )
