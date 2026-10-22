-- Prove2me | solution 1 for SidB.holder_trick
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:59:05.375994+00:00
-- url     : https://prove2.me/submissions/bcc933a3-4945-4edb-a643-effd224df5c3

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper
open SidB

lemma g73s_map_trans {α : Type} [DecidableEq α] (π τ : Equiv.Perm α) (T : Finset α) :
    T.map (π.trans τ).toEmbedding = (T.map π.toEmbedding).map τ.toEmbedding := by
  rw [Finset.map_map]; rfl

lemma g73s_fiber_eq {α : Type} [Fintype α] [DecidableEq α] (T S : Finset α) (hS : S.card = T.card) :
    (Finset.univ.filter (fun π : Equiv.Perm α => T.map π.toEmbedding = S)).card =
    (Finset.univ.filter (fun π : Equiv.Perm α => T.map π.toEmbedding = T)).card := by
  have hc : Fintype.card {x // x ∈ S} = Fintype.card {x // x ∈ T} := by
    simp [Fintype.card_coe, hS]
  set e := Fintype.equivOfCardEq hc
  set τ : Equiv.Perm α := e.extendSubtype
  have hsub : S.map τ.toEmbedding ⊆ T := by
    intro y hy
    simp only [Finset.mem_map, Equiv.coe_toEmbedding] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Equiv.extendSubtype_mem e x hx
  have hST : S.map τ.toEmbedding = T :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hS])
  have hTS : T.map τ.symm.toEmbedding = S := by
    rw [← hST, Finset.map_map]; ext x; simp
  apply Finset.card_nbij' (fun π => π.trans τ) (fun π => π.trans τ.symm)
  · intro π hπ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
    rw [g73s_map_trans, hπ, hST]
  · intro π hπ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
    rw [g73s_map_trans, hπ, hTS]
  · intro π _; ext x; simp
  · intro π _; ext x; simp

lemma g73s_L1 {α : Type} [Fintype α] [DecidableEq α] (r : Finset α → ℝ) (hr : ∀ s, 0 ≤ r s)
    (T : Finset α) :
    ∏ π : Equiv.Perm α, r (T.map π.toEmbedding) ^ (1 / (Fintype.card (Equiv.Perm α) : ℝ)) =
      ∏ S ∈ Finset.powersetCard T.card Finset.univ,
        r S ^ (1 / ((Fintype.card α).choose T.card : ℝ)) := by
  set N := Fintype.card (Equiv.Perm α)
  set c := (Finset.univ.filter (fun π : Equiv.Perm α => T.map π.toEmbedding = T)).card
  have hmaps : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm α)),
      T.map π.toEmbedding ∈ Finset.powersetCard T.card Finset.univ := by
    intro π _; simp
  have hN : N = (Fintype.card α).choose T.card * c := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm α => T.map π.toEmbedding)
      (s := Finset.univ) (t := Finset.powersetCard T.card Finset.univ) (fun π hπ => hmaps π hπ)
    change Fintype.card (Equiv.Perm α) = _
    rw [← Finset.card_univ, this, Finset.sum_congr rfl (g := fun _ => c), Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, smul_eq_mul]
    intro S hS
    rw [Finset.mem_powersetCard_univ] at hS
    exact g73s_fiber_eq T S hS
  have hNpos : 0 < N := Fintype.card_pos
  rw [← Finset.prod_fiberwise_of_maps_to hmaps]
  apply Finset.prod_congr rfl
  intro S hS
  rw [Finset.mem_powersetCard_univ] at hS
  rw [Finset.prod_congr rfl (g := fun _ => r S ^ (1 / (N : ℝ))), Finset.prod_const,
    g73s_fiber_eq T S hS, ← Real.rpow_natCast, ← Real.rpow_mul (hr S)]
  · show (r S) ^ ((1 / (N : ℝ)) * (c : ℝ)) = _
    congr 1
    have hC : (0 : ℝ) < (Fintype.card α).choose T.card := by
      have : 0 < (Fintype.card α).choose T.card := by
        rcases Nat.eq_zero_or_pos ((Fintype.card α).choose T.card) with h | h
        · rw [h] at hN; omega
        · exact h
      exact_mod_cast this
    have hc : (0 : ℝ) < c := by
      have : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · rw [h] at hN; omega
        · exact h
      exact_mod_cast this
    have hN' : (N : ℝ) = (Fintype.card α).choose T.card * c := by exact_mod_cast hN
    rw [hN']; field_simp
  · intro π hπ
    simp only [Finset.mem_filter] at hπ
    rw [hπ.2]

lemma g73s_L2 {α B : Type} [Fintype α] [DecidableEq α] [Fintype B] (r : Finset α → ℝ)
    (hr : ∀ s, 0 ≤ r s) (hr0 : r ∅ = 1) (T : B → Finset α) (D : ℕ) (hD : ∀ b, (T b).card ≤ D) :
    ∏ s : {s : Finset α // 0 < s.card ∧ s.card ≤ D},
        r s.1 ^ (((Finset.univ.filter (fun b => (T b).card = s.1.card)).card : ℝ) /
          ((Fintype.card α).choose s.1.card : ℝ)) =
      ∏ π : Equiv.Perm α, (∏ b, r ((T b).map π.toEmbedding)) ^
        (1 / (Fintype.card (Equiv.Perm α) : ℝ)) := by
  set d : Finset α → ℕ := fun S => (Finset.univ.filter (fun b => (T b).card = S.card)).card with hd
  set f : Finset α → ℝ := fun S => r S ^ (1 / ((Fintype.card α).choose S.card : ℝ)) with hf
  have lhs : ∀ S : Finset α, r S ^ ((d S : ℝ) / ((Fintype.card α).choose S.card : ℝ)) = f S ^ d S := by
    intro S
    rw [hf]; dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hr _)]
    congr 1; ring
  have e1 : ∏ s : {s : Finset α // 0 < s.card ∧ s.card ≤ D},
        r s.1 ^ (((Finset.univ.filter (fun b => (T b).card = s.1.card)).card : ℝ) /
          ((Fintype.card α).choose s.1.card : ℝ)) = ∏ S, f S ^ d S := by
    rw [Finset.prod_congr rfl (fun s _ => lhs s.1)]
    rw [← Finset.prod_subtype (Finset.univ.filter (fun S : Finset α => 0 < S.card ∧ S.card ≤ D))
      (p := fun S => 0 < S.card ∧ S.card ≤ D) (by simp) (fun S => f S ^ d S)]
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro S _ hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_lt, not_le] at hS
    rcases hS with h | h
    · have : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst this
      simp [hf, hr0]
    · have : d S = 0 := by
        rw [hd]; dsimp only
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro b _ hb
        have := hD b; omega
      rw [this, pow_zero]
  rw [e1]
  rw [Finset.prod_congr rfl (fun (π : Equiv.Perm α) _ => (Real.finsetProd_rpow Finset.univ
    (fun b => r ((T b).map π.toEmbedding)) (fun b _ => hr _) _).symm)]
  rw [Finset.prod_comm]
  rw [Finset.prod_congr rfl (fun b _ => g73s_L1 r hr (T b))]
  have e2 : ∀ b, ∏ S ∈ Finset.powersetCard (T b).card Finset.univ,
      r S ^ (1 / ((Fintype.card α).choose (T b).card : ℝ)) =
      ∏ S ∈ Finset.powersetCard (T b).card Finset.univ, f S := by
    intro b
    apply Finset.prod_congr rfl
    intro S hS
    rw [Finset.mem_powersetCard_univ] at hS
    rw [hf]; dsimp only; rw [hS]
  rw [Finset.prod_congr rfl (fun b _ => e2 b)]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun S => Finset.univ.filter (fun b => (T b).card = S.card))]
  · apply Finset.prod_congr rfl
    intro S _
    rw [Finset.prod_const]
  · intro b S
    simp [Finset.mem_powersetCard_univ, eq_comm]

lemma g73s_exp_nonneg (g : Graphon) (S : Type) [Fintype S] (f : (S → g.dom) → ℝ)
    (h : ∀ x, 0 ≤ f x) : 0 ≤ g.EX S f := by
  have h0 := g.exp_linear S inferInstance 0 0 (fun _ => 1) (fun _ => 1)
  simp only [zero_mul, add_zero] at h0
  have h1 := g.exp_mono S inferInstance (fun _ => 0) f h
  unfold Graphon.EX
  linarith

lemma g73s_rho_nonneg (g : Graphon) {A : Type} (F : Finset A) (x : A → g.dom) : 0 ≤ g.rho F x := by
  unfold Graphon.rho
  exact g73s_exp_nonneg g Unit _ (fun u => Finset.prod_nonneg (fun i _ => g.w_nonneg _ _))

lemma g73s_rho_empty (g : Graphon) {A : Type} (x : A → g.dom) : g.rho (∅ : Finset A) x = 1 := by
  unfold Graphon.rho Graphon.EX
  simp only [Finset.prod_empty]
  exact g.exp_one Unit _

lemma g73s_rho_map (g : Graphon) {X Y : Type} (e : X ≃ Y) (F : Finset X) (x : Y → g.dom) :
    g.rho (F.map e.toEmbedding) x = g.rho F (fun a => x (e a)) := by
  unfold Graphon.rho
  simp only [Finset.prod_map]
  rfl

theorem solution (g : Graphon) {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B)
    (α : ℕ → ℝ)
    (hα : ∀ k, 1 ≤ k → k ≤ H.maxDeg → α k = (H.degCount k : ℝ) / (Fintype.card A).choose k) :
    g.downsetDens (Fintype.card A) H.maxDeg α ≤ g.dens H := by
  set n := Fintype.card A with hn
  set eA : A ≃ Fin n := Fintype.equivFin A
  set T : B → Finset (Fin n) := fun b => (H.nbr b).map eA.toEmbedding with hT
  have hTc : ∀ b, (T b).card = (H.nbr b).card := fun b => Finset.card_map _
  have hD : ∀ b, (T b).card ≤ H.maxDeg := by
    intro b; rw [hTc]
    exact Finset.le_sup (f := fun b => (H.nbr b).card) (Finset.mem_univ b)
  set t := g.EX (Fin n) (fun y => ∏ b, g.rho (T b) y) with ht
  -- step 1: the density of H, transported to Fin n
  have h1 : g.dens H = t := by
    have := g.exp_transport (Fin n) A inferInstance inferInstance eA.symm
      (fun x => ∏ b, g.rho (H.nbr b) x)
    rw [ht]; unfold Graphon.dens Graphon.EX
    rw [← this]
    congr 1; funext y
    apply Finset.prod_congr rfl
    intro b _
    rw [hT]; dsimp only
    rw [g73s_rho_map]
    simp
  -- step 2: the downset density with explicit exponents
  have h2 : g.downsetDens n H.maxDeg α = g.EX (Fin n) (fun y =>
      ∏ s : {s : Finset (Fin n) // 0 < s.card ∧ s.card ≤ H.maxDeg},
        g.rho s.1 y ^ (((Finset.univ.filter (fun b => (T b).card = s.1.card)).card : ℝ) /
          ((Fintype.card (Fin n)).choose s.1.card : ℝ))) := by
    unfold Graphon.downsetDens
    congr 1; funext y
    apply Finset.prod_congr rfl
    intro s _
    rw [hα s.1.card s.2.1 s.2.2, Fintype.card_fin]
    congr 3
    simp only [Bigraph.degCount, hTc]
  -- step 3: symmetrization and Hoelder
  set N := Fintype.card (Equiv.Perm (Fin n)) with hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Fintype.card_pos : 0 < N)
  have tnn : 0 ≤ t := g73s_exp_nonneg g _ _ (fun y => Finset.prod_nonneg (fun b _ => g73s_rho_nonneg g _ y))
  rw [h1, h2]
  have h3 : g.EX (Fin n) (fun y =>
      ∏ s : {s : Finset (Fin n) // 0 < s.card ∧ s.card ≤ H.maxDeg},
        g.rho s.1 y ^ (((Finset.univ.filter (fun b => (T b).card = s.1.card)).card : ℝ) /
          ((Fintype.card (Fin n)).choose s.1.card : ℝ))) =
      g.exp (Fin n) inferInstance (fun y => ∏ π : Equiv.Perm (Fin n),
        (fun π y => (∏ b, g.rho ((T b).map π.toEmbedding) y) ^ (1 / (N : ℝ))) π y) := by
    unfold Graphon.EX
    congr 1; funext y
    exact g73s_L2 (fun s => g.rho s y) (fun s => g73s_rho_nonneg g s y) (g73s_rho_empty g y) T
      H.maxDeg hD
  rw [h3]
  refine le_trans (g.exp_holder (Fin n) inferInstance (Equiv.Perm (Fin n)) inferInstance _
    (fun π y => Real.rpow_nonneg (Finset.prod_nonneg (fun b _ => g73s_rho_nonneg g _ y)) _)
    Fintype.card_pos) (le_of_eq ?_)
  have h4 : ∀ π : Equiv.Perm (Fin n),
      g.exp (Fin n) inferInstance (fun y =>
        ((fun π y => (∏ b, g.rho ((T b).map π.toEmbedding) y) ^ (1 / (N : ℝ))) π y) ^
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) = t := by
    intro π
    have htr := g.exp_transport (Fin n) (Fin n) inferInstance inferInstance π.symm
      (fun y => ∏ b, g.rho (T b) y)
    rw [ht]; unfold Graphon.EX
    rw [← htr]
    congr 1; funext y
    dsimp only
    rw [← hN, one_div, Real.rpow_inv_rpow (Finset.prod_nonneg (fun b _ => g73s_rho_nonneg g _ y))
      hNpos.ne']
    apply Finset.prod_congr rfl
    intro b _
    rw [g73s_rho_map]
    simp
  rw [Finset.prod_congr rfl (fun π _ => by rw [h4 π]), Finset.prod_const, Finset.card_univ, ← hN,
    ← Real.rpow_natCast, ← Real.rpow_mul tnn, one_div, inv_mul_cancel₀ hNpos.ne', Real.rpow_one]
