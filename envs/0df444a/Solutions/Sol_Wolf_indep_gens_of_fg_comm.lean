-- Prove2me | solution 1 for Wolf.indep_gens_of_fg_comm
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-22T19:23:56.143001+00:00
-- url     : https://prove2.me/submissions/e0bc6dfe-7d87-42e4-b6af-e21591ad0474

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Order.SupIndep
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

set_option autoImplicit false

open scoped BigOperators

/-- Independence of a family of subgroups is preserved under an injective
monoid homomorphism (applied via `Subgroup.map`). -/
theorem iSupIndep_map_of_injective {ι : Sort*} {H G : Type*} [Group H] [Group G]
    {s : ι → Subgroup H} (hs : iSupIndep s) {φ : H →* G} (hφ : Function.Injective φ) :
    iSupIndep (fun i => (s i).map φ) := by
  intro i
  have h := hs i
  rw [disjoint_iff_inf_le] at h ⊢
  have h2 : (⨆ (j) (_ : j ≠ i), (s j).map φ) = (⨆ (j) (_ : j ≠ i), s j).map φ := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun j => (Subgroup.map_iSup φ _).symm
  rw [h2, ← Subgroup.map_inf _ _ φ hφ, ← Subgroup.map_bot φ]
  exact Subgroup.map_mono h

-- Reindexing an independent family along an equivalence.
theorem iSupIndep_equiv_comp {ι κ : Sort*} {G : Type*} [Group G]
    {s : κ → Subgroup G} (hs : iSupIndep s) (e : ι ≃ κ) :
    iSupIndep (fun i => s (e i)) := by
  intro i
  have h := hs (e i)
  have hsup : (⨆ j : ι, ⨆ (_ : j ≠ i), s (e j)) =
      (⨆ k : κ, ⨆ (_ : k ≠ e i), s k) := by
    calc (⨆ j : ι, ⨆ (_ : j ≠ i), s (e j))
        = ⨆ k : κ, ⨆ (_ : e.symm k ≠ i), s (e (e.symm k)) :=
          (Equiv.iSup_comp (g := fun j : ι => ⨆ (_ : j ≠ i), s (e j)) e.symm).symm
      _ = (⨆ k : κ, ⨆ (_ : k ≠ e i), s k) := by
          apply iSup_congr
          intro k
          have hprop : (e.symm k ≠ i) = (k ≠ e i) := by
            apply propext
            constructor
            · intro h1 h2
              exact h1 (h2 ▸ e.symm_apply_apply i)
            · intro h1 h2
              exact h1 (e.apply_symm_apply k ▸ congrArg e h2)
          rw [hprop, e.apply_symm_apply]
  rw [disjoint_iff_inf_le] at h ⊢
  rw [hsup]
  exact h

theorem solution {G : Type*} [Group G] [IsMulCommutative G] [Group.FG G] :
    ∃ (n : ℕ) (f : Fin n → G),
      iSupIndep (fun i => Subgroup.zpowers (f i)) ∧
      (⨆ i, Subgroup.zpowers (f i)) = ⊤ := by
  classical
  -- Step 1: structure theorem gives an isomorphism to a finite product.
  obtain ⟨ι, j, hι, hj, p, hp, e, ⟨iso⟩⟩ := by
    letI hComm : CommGroup G :=
      CommGroup.mk (toGroup := ‹Group G›) (mul_comm := fun a b => mul_comm' a b)
    have hFG : @Group.FG G hComm.toGroup := ‹Group.FG G›
    exact @CommGroup.equiv_free_prod_prod_multiplicative_zmod G hComm hFG
  -- Step 2: coordinate generators in the product.
  -- H = (j → Multiplicative ℤ) × ((i:ι) → Multiplicative (ZMod (p i ^ e i)))
  let g : j ⊕ ι → ((j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) :=
    Sum.elim (fun a => (Pi.mulSingle a (Multiplicative.ofAdd 1), 1))
      (fun b => (1, Pi.mulSingle b (Multiplicative.ofAdd 1)))
  -- Step 3: the coordinate subgroups are independent.
  have hindep : iSupIndep (fun k : j ⊕ ι => Subgroup.zpowers (g k)) := by
    intro k
    cases k with
    | inl a =>
      -- Project to the a-th free coordinate.
      let φ : ((j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) →*
          Multiplicative ℤ :=
        (Pi.evalMonoidHom _ a).comp (MonoidHom.fst _ _)
      -- All other generators lie in the kernel.
      have hφ : ∀ k' : j ⊕ ι, k' ≠ Sum.inl a → φ (g k') = 1 := by
        intro k' hk'
        cases k' with
        | inl a' =>
          have haa : a' ≠ a := fun h => hk' (congrArg Sum.inl h)
          show (Pi.mulSingle (M := fun _ : j => Multiplicative ℤ) a' (Multiplicative.ofAdd (1 : ℤ))) a = 1
          exact Pi.mulSingle_eq_of_ne' haa _
        | inr b =>
          show ((1 : j → Multiplicative ℤ) a) = 1
          rfl
      have hJ : (⨆ (k') (_ : k' ≠ Sum.inl a), Subgroup.zpowers (g k')) ≤ φ.ker := by
        refine iSup_le fun k' => iSup_le fun hk' => ?_
        rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
        exact hφ k' hk'
      -- The a-th generator is disjoint from the kernel.
      have hD : Disjoint (Subgroup.zpowers (g (Sum.inl a))) φ.ker := by
        rw [disjoint_iff_inf_le, le_bot_iff, Subgroup.eq_bot_iff_forall]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hx, hxker⟩ := hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [MonoidHom.mem_ker] at hxker
        have hpow : ∀ (y : j → Multiplicative ℤ) (c : j) (m : ℤ),
            ((y ^ m) c) = (y c) ^ m :=
          fun y c m => (map_zpow (Pi.evalMonoidHom _ c) y m).symm
        have h1 : (((g (Sum.inl a)) ^ n).1 : j → Multiplicative ℤ) = 1 := by
          show (Pi.mulSingle (M := fun _ : j => Multiplicative ℤ) a (Multiplicative.ofAdd (1 : ℤ))) ^ n = 1
          funext a'
          by_cases haa : a' = a
          · subst haa
            exact hxker
          · rw [hpow _ _ _, Pi.mulSingle_eq_of_ne haa, one_zpow, Pi.one_apply]
        have h2 : (((g (Sum.inl a)) ^ n).2 : (i : ι) → Multiplicative (ZMod (p i ^ e i))) = 1 := by
          show (1 : (i : ι) → Multiplicative (ZMod (p i ^ e i))) ^ n = 1
          rw [one_zpow]
        exact Prod.ext h1 h2
      exact hD.mono_right hJ
    | inr b =>
      -- Project to the b-th torsion coordinate.
      let φ : ((j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) →*
          Multiplicative (ZMod (p b ^ e b)) :=
        (Pi.evalMonoidHom _ b).comp (MonoidHom.snd _ _)
      -- All other generators lie in the kernel.
      have hφ : ∀ k' : j ⊕ ι, k' ≠ Sum.inr b → φ (g k') = 1 := by
        intro k' hk'
        cases k' with
        | inl a =>
          show ((1 : (i : ι) → Multiplicative (ZMod (p i ^ e i))) b) = 1
          rfl
        | inr b' =>
          have hbb : b' ≠ b := fun h => hk' (congrArg Sum.inr h)
          show ((Pi.mulSingle (M := fun i : ι => Multiplicative (ZMod (p i ^ e i))) b'
            (Multiplicative.ofAdd (1 : ZMod (p b' ^ e b')))) b) = 1
          exact Pi.mulSingle_eq_of_ne' hbb _
      have hJ : (⨆ (k') (_ : k' ≠ Sum.inr b), Subgroup.zpowers (g k')) ≤ φ.ker := by
        refine iSup_le fun k' => iSup_le fun hk' => ?_
        rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
        exact hφ k' hk'
      -- The b-th generator is disjoint from the kernel.
      have hD : Disjoint (Subgroup.zpowers (g (Sum.inr b))) φ.ker := by
        rw [disjoint_iff_inf_le, le_bot_iff, Subgroup.eq_bot_iff_forall]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hx, hxker⟩ := hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [MonoidHom.mem_ker] at hxker
        have hpow : ∀ (y : (i : ι) → Multiplicative (ZMod (p i ^ e i))) (c : ι) (m : ℤ),
            ((y ^ m) c) = (y c) ^ m :=
          fun y c m => (map_zpow (Pi.evalMonoidHom _ c) y m).symm
        have h1 : (((g (Sum.inr b)) ^ n).1 : j → Multiplicative ℤ) = 1 := by
          show (1 : j → Multiplicative ℤ) ^ n = 1
          rw [one_zpow]
        have h2 : (((g (Sum.inr b)) ^ n).2 : (i : ι) → Multiplicative (ZMod (p i ^ e i))) = 1 := by
          show ((Pi.mulSingle (M := fun i : ι => Multiplicative (ZMod (p i ^ e i))) b
            (Multiplicative.ofAdd (1 : ZMod (p b ^ e b)))) ^ n) = 1
          funext b'
          by_cases hbb : b' = b
          · subst hbb
            exact hxker
          · rw [hpow _ _ _, Pi.mulSingle_eq_of_ne hbb, one_zpow, Pi.one_apply]
        exact Prod.ext h1 h2
      exact hD.mono_right hJ
  -- Step 4: the coordinate subgroups span the whole product.
  have hspan : (⨆ k : j ⊕ ι, Subgroup.zpowers (g k)) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    rintro ⟨x, y⟩
    have hmem : ∀ k : j ⊕ ι, g k ∈ (⨆ k, Subgroup.zpowers (g k)) := by
      intro k
      have hle : Subgroup.zpowers (g k) ≤ (⨆ k, Subgroup.zpowers (g k)) :=
        le_iSup (fun k => Subgroup.zpowers (g k)) k
      exact SetLike.le_def.mp hle (Subgroup.mem_zpowers (g k))
    have hpow1 : ∀ (u : j → Multiplicative ℤ) (c : j) (m : ℤ), ((u ^ m) c) = (u c) ^ m :=
      fun u c m => (map_zpow (Pi.evalMonoidHom _ c) u m).symm
    have hpow2 : ∀ (v : (i:ι) → Multiplicative (ZMod (p i ^ e i))) (c : ι) (m : ℤ),
        ((v ^ m) c) = (v c) ^ m :=
      fun v c m => (map_zpow (Pi.evalMonoidHom _ c) v m).symm
    -- Each torsion coordinate is a power of the corresponding generator.
    have hexp : ∀ b : ι, (Multiplicative.ofAdd (1 : ZMod (p b ^ e b))) ^
        (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ) = y b := by
      intro b
      haveI : NeZero (p b ^ e b) := ⟨pow_ne_zero _ (Nat.Prime.ne_zero (hp b))⟩
      rw [zpow_natCast]
      show Multiplicative.ofAdd (((Multiplicative.toAdd (y b)).val) • (1 : ZMod (p b ^ e b))) = y b
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      rfl
    -- The free part (x, 1): x is a product of the free generators.
    have hfree : ((x, 1) : (j → Multiplicative ℤ) × ((i:ι) → Multiplicative (ZMod (p i ^ e i)))) ∈
        (⨆ k, Subgroup.zpowers (g k)) := by
      have hprod : ((x, 1) : (j → Multiplicative ℤ) × ((i:ι) → Multiplicative (ZMod (p i ^ e i)))) =
          Finset.prod Finset.univ (fun a => (g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))) := by
        -- First, rewrite the fst projection of the product
        have hfst : (Finset.prod Finset.univ (fun a => (g (Sum.inl a)) ^ (Multiplicative.toAdd (x a)))).1 =
            Finset.prod Finset.univ (fun a => (((g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))).1)) :=
          map_prod (MonoidHom.fst _ _) (fun a => (g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))) Finset.univ
        have hsnd : (Finset.prod Finset.univ (fun a => (g (Sum.inl a)) ^ (Multiplicative.toAdd (x a)))).2 =
            Finset.prod Finset.univ (fun a => (((g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))).2)) :=
          map_prod (MonoidHom.snd _ _) (fun a => (g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))) Finset.univ
        apply Prod.ext
        · funext a'
          show x a' = ((Finset.prod Finset.univ (fun a => (g (Sum.inl a)) ^ (Multiplicative.toAdd (x a)))).1) a'
          rw [hfst, Finset.prod_apply, Finset.prod_eq_single a']
          · have hga : (((g (Sum.inl a')) ^ (Multiplicative.toAdd (x a'))).1) a' = x a' := by
              have e1 : ((g (Sum.inl a')) ^ (Multiplicative.toAdd (x a'))).1 =
                  (Pi.mulSingle (M := fun _ : j => Multiplicative ℤ) a'
                    (Multiplicative.ofAdd (1 : ℤ))) ^ (Multiplicative.toAdd (x a')) := rfl
              rw [e1, hpow1, Pi.mulSingle_eq_same]
              -- (ofAdd 1) ^ (toAdd (x a')) = x a'
              have h2 : (Multiplicative.ofAdd (1 : ℤ)) ^ (Multiplicative.toAdd (x a')) = x a' := by
                show Multiplicative.ofAdd ((Multiplicative.toAdd (x a')) • (1 : ℤ)) = x a'
                rw [smul_eq_mul, mul_one]
                rfl
              exact h2
            exact hga.symm
          · intro a _ haa
            have hga : ((((g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))).1)) a' = 1 := by
              have e1 : ((g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))).1 =
                  (Pi.mulSingle (M := fun _ : j => Multiplicative ℤ) a
                    (Multiplicative.ofAdd (1 : ℤ))) ^ (Multiplicative.toAdd (x a)) := rfl
              rw [e1, hpow1, Pi.mulSingle_eq_of_ne haa.symm, one_zpow]
            exact hga
          · intro ha
            exact absurd (Finset.mem_univ a') ha
        · show (1 : (i:ι) → Multiplicative (ZMod (p i ^ e i))) =
              ((Finset.prod Finset.univ (fun a => (g (Sum.inl a)) ^ (Multiplicative.toAdd (x a)))).2)
          rw [hsnd]
          have h1 : ∀ a : j, ((g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))).2 = 1 := by
            intro a
            have e1 : ((g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))).2 = (1 : (i:ι) → Multiplicative (ZMod (p i ^ e i))) ^ (Multiplicative.toAdd (x a)) := rfl
            rw [e1, one_zpow]
          calc (1 : (i:ι) → Multiplicative (ZMod (p i ^ e i)))
              = Finset.prod Finset.univ (fun _ : j => (1 : (i:ι) → Multiplicative (ZMod (p i ^ e i)))) := by
                simp [Finset.prod_const_one]
            _ = Finset.prod Finset.univ (fun a => ((g (Sum.inl a)) ^ (Multiplicative.toAdd (x a))).2) := by
                apply Finset.prod_congr rfl
                intro a _
                exact (h1 a).symm
      rw [hprod]
      exact Subgroup.prod_mem _ (fun a _ => Subgroup.zpow_mem _ (hmem _) _)
    -- The torsion part (1, y): similar.
    have htors : ((1, y) : (j → Multiplicative ℤ) × ((i:ι) → Multiplicative (ZMod (p i ^ e i)))) ∈
        (⨆ k, Subgroup.zpowers (g k)) := by
      have hprod : ((1, y) : (j → Multiplicative ℤ) × ((i:ι) → Multiplicative (ZMod (p i ^ e i)))) =
          Finset.prod Finset.univ (fun b =>
            (g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)) := by
        have hfst : (Finset.prod Finset.univ (fun b =>
            (g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ))).1 =
            Finset.prod Finset.univ (fun b =>
              (((g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)).1)) :=
          map_prod (MonoidHom.fst _ _)
            (fun b => (g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)) Finset.univ
        have hsnd : (Finset.prod Finset.univ (fun b =>
            (g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ))).2 =
            Finset.prod Finset.univ (fun b =>
              (((g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)).2)) :=
          map_prod (MonoidHom.snd _ _)
            (fun b => (g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)) Finset.univ
        apply Prod.ext
        · show (1 : j → Multiplicative ℤ) =
              ((Finset.prod Finset.univ (fun b =>
                (g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ))).1)
          rw [hfst]
          have h1 : ∀ b : ι, ((g (Sum.inr b)) ^
              (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)).1 = 1 := by
            intro b
            have e1 : ((g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)).1 =
                (1 : j → Multiplicative ℤ) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ) := rfl
            rw [e1, one_zpow]
          calc (1 : j → Multiplicative ℤ)
              = Finset.prod Finset.univ (fun _ : ι => (1 : j → Multiplicative ℤ)) := by
                simp [Finset.prod_const_one]
            _ = Finset.prod Finset.univ (fun b =>
                (((g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)).1)) := by
                apply Finset.prod_congr rfl
                intro b _
                exact (h1 b).symm
        · funext b'
          show y b' = ((Finset.prod Finset.univ (fun b =>
            (g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ))).2) b'
          rw [hsnd, Finset.prod_apply, Finset.prod_eq_single b']
          · have hgb : (((g (Sum.inr b')) ^
                (((Multiplicative.toAdd (y b')).val : ℕ) : ℤ)).2) b' = y b' := by
              have e1 : ((g (Sum.inr b')) ^ (((Multiplicative.toAdd (y b')).val : ℕ) : ℤ)).2 =
                  (Pi.mulSingle (M := fun i : ι => Multiplicative (ZMod (p i ^ e i))) b'
                    (Multiplicative.ofAdd 1)) ^ (((Multiplicative.toAdd (y b')).val : ℕ) : ℤ) := rfl
              rw [e1, hpow2, Pi.mulSingle_eq_same]
              exact hexp b'
            exact hgb.symm
          · intro b _ hbb
            have hgb : ((((g (Sum.inr b)) ^
                (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)).2)) b' = 1 := by
              have e1 : ((g (Sum.inr b)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ)).2 =
                  (Pi.mulSingle (M := fun i : ι => Multiplicative (ZMod (p i ^ e i))) b
                    (Multiplicative.ofAdd 1)) ^ (((Multiplicative.toAdd (y b)).val : ℕ) : ℤ) := rfl
              rw [e1, hpow2, Pi.mulSingle_eq_of_ne hbb.symm, one_zpow]
            exact hgb
          · intro ha
            exact absurd (Finset.mem_univ b') ha
      rw [hprod]
      exact Subgroup.prod_mem _ (fun b _ => Subgroup.zpow_mem _ (hmem _) _)
    -- Combine: (x, y) = (x, 1) * (1, y)
    have hmem_prod := (⨆ k, Subgroup.zpowers (g k)).mul_mem hfree htors
    simpa using hmem_prod
  -- Step 5: transport back to G and reindex to Fin n
  have hφ : Function.Injective (iso.symm.toMonoidHom : _ →* G) := iso.symm.injective
  have hindepG : iSupIndep (fun k : j ⊕ ι => Subgroup.zpowers (iso.symm (g k))) := by
    have h := iSupIndep_map_of_injective hindep hφ
    simpa [MonoidHom.map_zpowers] using h
  have hspanG : (⨆ k : j ⊕ ι, Subgroup.zpowers (iso.symm (g k))) = ⊤ := by
    have h : (⨆ k : j ⊕ ι, (Subgroup.zpowers (g k)).map iso.symm.toMonoidHom) = ⊤ := by
      rw [← Subgroup.map_iSup, hspan]
      exact Subgroup.map_top_of_surjective _ iso.symm.surjective
    simpa [MonoidHom.map_zpowers] using h
  classical
  let efin := Fintype.equivFin (j ⊕ ι)
  refine ⟨Fintype.card (j ⊕ ι), fun i => iso.symm (g (efin.symm i)), ?_, ?_⟩
  · have h := iSupIndep_equiv_comp hindepG efin.symm
    simpa using h
  · have h : (⨆ i : Fin (Fintype.card (j ⊕ ι)),
        Subgroup.zpowers (iso.symm (g (efin.symm i)))) =
        (⨆ k : j ⊕ ι, Subgroup.zpowers (iso.symm (g k))) :=
      Equiv.iSup_comp (g := fun k : j ⊕ ι => Subgroup.zpowers (iso.symm (g k))) efin.symm
    rw [h]
    exact hspanG
